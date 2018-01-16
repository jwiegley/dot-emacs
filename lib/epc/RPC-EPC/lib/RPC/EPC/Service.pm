package RPC::EPC::Service;

use warnings;
use strict;
use utf8;
use Carp;

use version; our $VERSION = qv('0.0.11');

use base 'Exporter';

our @EXPORT = qw(
   to_sexp
);

use Encode;
use AnyEvent;
use AnyEvent::Socket;
use AnyEvent::Handle;
use Data::SExpression;
use Data::SExpression::Symbol;
use B;
use Data::Dumper; # for debug


##################################################
# sexp encoding
# (This code is based on Mojolicious's JSON library.)

# Translate an argument object into S-expression text.
sub to_sexp {
  my $arg = shift;
  if (ref $arg eq 'HASH') {
    return _to_sexp_hash($arg);
  } elsif (ref $arg eq 'ARRAY') {
    return _to_sexp_list($arg);
  }
  my $flags = B::svref_2object(\$arg)->FLAGS;
  if ($flags & (B::SVp_IOK | B::SVp_NOK) && !($flags & B::SVp_POK)) {
    return _to_sexp_num($arg);
  } else {
    return _to_sexp_string($arg);
  }
}


# for elisp's prin1 escape
my %ESCAPE = (
  '"'     => '"',
  '\\'    => '\\',
);

my %REVERSE;
for my $key (keys %ESCAPE) { $REVERSE{$ESCAPE{$key}} = "\\$key" }

sub _to_sexp_string {
  my $string = shift;
  return "nil" unless $string;

  # Escape
  $string =~ s/([\\\"])/$REVERSE{$1}/gs;

  $string = Encode::encode_utf8($string) if Encode::is_utf8($string);

  # Stringify
  return "\"$string\"";
}

sub _to_sexp_num {
  return shift;
}

sub _to_sexp_list {
  my $list = shift;
  my @out = map {to_sexp $_} @$list;
  return "(" . join(" ", @out) . ")";
}

sub _to_sexp_hash {
  my $hash = shift;
  my $out = [];
  foreach my $key ( keys %$hash ) {
    push @$out, "(".to_sexp($key)." . ".to_sexp($hash->{$key}).")";
  }
  return "(" . join(" ", @$out) . ")";
}

##################################################
# nil to undef

our $NIL = Data::SExpression::Symbol->new("nil");

sub _nil_to_undef {
  my $arg = shift;
  if (ref $arg eq 'HASH') {
    return _nil_to_undef_hash($arg);
  } elsif (ref $arg eq 'ARRAY') {
    return _nil_to_undef_list($arg);
  }
  return if ($NIL eq $arg);
  return $arg;
}

sub _nil_to_undef_list {
  my $list = shift;
  for (my $i = 0; $i < @$list; $i++) {
    $list->[$i] = _nil_to_undef($list->[$i]);
  }
  return $list;
}

sub _nil_to_undef_hash {
  my $hash = shift;
  foreach my $key ( keys %$hash ) {
    $hash->{$key} = _nil_to_undef($hash->{$key});
  }
  return $hash;
}

sub _correct_method_spec {
  my $a = shift;
  if (ref($a) eq "CODE") {
    return {'sub' => $a, 'arg_spec' => undef, 'docstring' => undef};
  } elsif (ref($a) eq "ARRAY") {
    my ($sub,$arg,$doc) = @$a;
    return {'sub' => $sub, 'arg_spec' => $arg, 'docstring' => $doc};
  } elsif (ref($a) eq "HASH") {
    return $a;
  } else {
    return $a;
  }
}

sub _correct_method_specs {
  my $methods = shift;
  my $ret = {};
  foreach my $key ( keys %$methods ) {
    $ret->{$key} = _correct_method_spec( $methods->{$key} );
  }
  return $ret;
}


##################################################
# Protocol Stacks

sub new {
  my ($class, $port, $methods) = @_;
  my $cv = AnyEvent->condvar;
  return bless { 'port' => $port,
                 'count' => 0,
                 'methods' => _correct_method_specs($methods),
                 'sessions' => {},
                 'wait' => $cv }, $class;
}

sub _register_event_loop {
  my ($self,$fh) = @_;

  my $ds = Data::SExpression->new({use_symbol_class=>1,fold_alists=>1});

  my $hdl; $hdl = new AnyEvent::Handle
    (fh => $fh,
     on_error => sub {
       my ($hdl, $fatal, $msg) = @_;
       AE::log warn => "got error $msg\n";
       $hdl->destroy;
       $self->{wait}->send;
     });
  $self->{handle} = $hdl;

  my $reading_buffer = "";
  my @reader; @reader =
    (line => sub {
       my ($hdl, $incoming) = @_;
       # print STDERR "INCOMING:$incoming";
       $reading_buffer .= $incoming . "\n";
       my $len = substr($reading_buffer, 0, 6);
       if (!$len =~ /[0-9a-f]{6}/i) {
         # print STDERR "Wrong length code: $reading_buffer\nAbort\n";
         AE::log warn => "Wrong length code: $reading_buffer\n";
         $hdl->destroy;
         $self->{wait}->send;
         return;
       }
       $len = hex($len);
       my $body = substr($reading_buffer, 6);
       if ($len > length $body) {
         # try next lines
         # print STDERR "lencode:$len / current:" . (length $body) . "\n";
         $hdl->push_read(@reader);
         return;
       }
       # print STDERR "Here len:$len / current:" . (length $body) . "\n";
       if ($len < length $body) {
         $reading_buffer = substr($body, $len+1);
         $body = substr($body, 0, $len);
       } else {
         $reading_buffer = "";
       }

       my ($text, $sexp);
       eval {
         ($sexp, $text) = $ds->read(Encode::decode_utf8($body));
       };
       # print STDERR "SEXP:".Dumper $sexp;
       if ($sexp->[0]) {
         if ($sexp->[0]->name eq "quit") {
           $hdl->destroy;
           $self->{wait}->send;
           return;
         }
       
         my $handler = $self->{handlers}->{shift(@$sexp)->name};
         if ($handler) {
           $handler->($sexp);
         }
       } else {
         # print STDERR 'NULL:'.Dumper $sexp;
       }
       $hdl->push_read(@reader);
     });

  $hdl->push_read(@reader);
}

sub _handle_connection {
  my ($self,$fh,$host,$port) = @_;
  
  my $handlers = {
      'call' => sub { $self->_call(@_); },
      'return' => sub { $self->_return(@_); },
      'return-error' => sub { $self->_return_error(@_); },
      'epc-error' => sub { $self->_epc_error(@_); },
      'methods' => sub { $self->_query_methods(@_); },
    };
  $self->{handlers} = $handlers;
  $self->_register_event_loop($fh);
}

sub _uid {
  my $self = shift;
  return $self->{count}++;
}

sub _send_message {
  my ($self, $message) = @_;
  my $hdl = $self->{handle};
  my $len = length($message) + 1;
  # print STDERR ">>> [$message]\n";
  $hdl->push_write(sprintf("%06x%s\n", $len, $message));
}

sub _call {
  my ($self, $sexp) = @_;
  # print STDERR "CALL:" . Dumper $sexp;
  my $id = shift(@$sexp);
  my $name = shift(@$sexp);
  my $task = $self->{methods}->{$name}->{sub};
  if ($task) {
    my $args = _nil_to_undef($sexp->[0]);
    eval {
      my $ret = $task->($args);
      if ((ref $ret) eq "AnyEvent::CondVar") {
        $ret = $ret->recv;
      }
      $self->_send_message("(return $id ".to_sexp($ret).")");
    };
    if ($@) {
      $self->_send_message("(return-error $id ".to_sexp($@).")");
    }
  } else {
    $self->_send_message("(epc-error $id \"Not found the method: $name\")");
  }
}

sub _return {
  my ($self, $sexp) = @_;
  # print STDERR "RET:" . Dumper $sexp;
  my $id = shift(@$sexp);
  my $result = _nil_to_undef($sexp);
  my $cv = $self->{sessions}->{$id};
  if ($cv) {
    delete $self->{sessions}->{$id};
    $cv->send($result->[0]);
  } else {
    print STDERR "Not found ID : $id\n";
  }
}

sub _return_error {
  my ($self, $sexp) = @_;
  # print STDERR "ERR-RET:" . Dumper $sexp;
  my $id = shift(@$sexp);
  my $result = $sexp->[0];
  my $cv = $self->{sessions}->{$id};
  if ($cv) {
    delete $self->{sessions}->{$id};
    $cv->croak(['ERROR',$result]);
  } else {
    print STDERR "Not found ID : $id\n";
  }
}

sub _epc_error {
  my ($self, $sexp) = @_;
  # print STDERR "EPCERR-RET:" . Dumper $sexp;
  my $id = shift(@$sexp);
  my $result = $sexp->[0];
  my $cv = $self->{sessions}->{$id};
  if ($cv) {
    delete $self->{sessions}->{$id};
    $cv->croak(['EPC_ERROR',$result]);
  } else {
    print STDERR "Not found ID : $id\n";
  }
}

sub _query_methods {
  my ($self, $sexp) = @_;
  # print STDERR "METHODS:" . Dumper $sexp;
  my $id = shift(@$sexp);
  eval {
    my @ret = ();
    my $hash = $self->{methods};
    # print STDERR "HASH:" . Dumper $hash;
    foreach my $key ( keys %$hash ) {
      my $method = $hash->{$key};
      push @ret, [$key, $method->{'arg_spec'}, $method->{'docstring'}];
    }

    $self->_send_message("(return $id ".to_sexp(\@ret).")");
  };
  if ($@) {
    $self->_send_message("(return-error $id ".to_sexp($@).")");
  }
}

sub call_method {
  my $self = shift;
  my $name = shift;
  my $args = shift;
  my $cv = AnyEvent->condvar;
  my $id = $self->_uid;
  $self->{sessions}->{$id} = $cv;
  $self->_send_message("(call $id $name ".(to_sexp $args).")");
  return $cv;
}

sub define_method {
  my $self = shift;
  my $name = shift;
  $self->{methods}->{$name} = _correct_method_spec(\@_);
}

sub query_methods {
  my $self = shift;
  my $cv = AnyEvent->condvar;
  my $id = $self->_uid;
  $self->{sessions}->{$id} = $cv;
  $self->_send_message("(methods $id)");
  return $cv;
}

sub start {
  my $self = shift;
  my $server = tcp_server undef, $self->{port}, sub {
    $self->_handle_connection(@_);
  }, sub {
    my ($fh, $thishost, $thisport) = @_;
	binmode( STDOUT, ":unix" ); # immediate flush
    print "$thisport\n"; # epc protocol
  };
  $self->{server} = $server;
  $self->{wait}->recv;
}

sub client_start {
  my $self = shift;
  my $host = "127.0.0.1";
  my $cv = AnyEvent->condvar;
  my $client = tcp_connect $host, $self->{port}, sub {
    my ($fh) = @_;
    if ($fh) {
      $self->_handle_connection($fh, $host, $self->{port});
      $cv->send;
    } else {
      $cv->croak(['Could not connect server.']);
    }
  };
  $self->{client} = $client;
  $cv->recv;
}

sub stop {
  my $self = shift;
  $self->{handle}->push_shutdown;
}



1; # Magic true value required at end of module
__END__

=head1 NAME

RPC::EPC::Service - An Asynchronous Remote Procedure Stack.


=head1 VERSION

This document describes RPC::EPC::Service version 0.0.11


=head1 SYNOPSIS

=head2 Server code

    use RPC::EPC::Service;
    
    my $server = RPC::EPC::Service->new(8888, {
        'add' => sub {
            my $args_ref = shift;
            my ($a,$b) = @$args_ref;
            return $a + $b;
        });
    $server->start;

=head2 Client code

    use RPC::EPC::Service;
    
    my $client = RPC::EPC::Service->new($port,{});
    $client->client_start;
    
    my $ret = $client->call_method('add', [1,2]);
    $ret->recv == 3;
    
    $client->stop;

=head1 DESCRIPTION

This module enables to connect the other process with the S-expression
protocol, like the Swank protocol of the SLIME.

SLIME : http://common-lisp.net/project/slime/

The primary objective is for users to make some Emacs extensions with
the Perl and CPAN.

=head2 Protocol

The encoding format is the S-expression.

The TCP socket is employed by the communication.

Because the RPC session is written in the async manner, the programs
can call the procedures asynchronously.

=head2 Object Serialization

This module can translate following types:

=over 4

=item *
undef

=item *
Number

=item *
String

=item *
Array

=item *
Hash

=item *
Complex of Array and Hash.

=back


=head1 INTERFACE

=head2 Server and Client Commons

=head3 C<new>

  $service = RPC::EPC::Service->new($port, $handlers);

Create a server object. If port number is 0 or undef, the number is
decided by the OS.

The C<$handlers> object is a hash of method names and sub blocks,
which methods are called by the peer process. Methods can be also 
defined by C<define_method> after the initialization.

=head3 define_method

  $service->define_method($method_name, sub { .... });

Define a method which is called by the peer process.

The following form defines a method with documents for the method
argument and specifications.

  $service->define_method($method_name,
      sub { .... },
      "arg1 arg2",
      "document for this method");

The documents are referred by the peer process for users to inspect the methods.

=head3 call_method

  $ret = $service->call_method($method_name, $args);
  print $ret->recv;

Call the peer's method. The arguments should be packed in one object,
such as Array and Hash.

This method returns immediately, not waiting for the result, and value
C<$ret> is C<AnyEvent::condvar> object. To obtain the result, the
program calls the C<recv> method, because the peer's task is executed
concurrently and the result is sent asynchronously.

The C<recv> method may raise the error. The error has two types, the
peer's program (Application Error) and the RPC stack (RPC Error).

The Application Error is a normal error which is caused by peer's
program, such as 'division by zero', 'file not found' and so on. The
programmers are responsible to this type errors, recovering error
handling or just fixing bugs.

The RPC Error is a communication error which is caused by RPC stack,
such as 'connection closed', 'method not found', 'serialization error'
and so on. This type errors are caused by environment problems, bugs
of peer's program, our side one or the RPC stack.

Here is a sample robust code:

  $ret = $service->call_method($method_name, $args);
  eval {
    print $ret->recv; # normal result
  };
  if ($@) {
    # Error handling
    if ($@->[0] eq "ERROR") {
      # Application Error
      print $@->[1];  # error message
    } elsif ($@->[0] eq "EPC-ERROR") {
      # RPC Error
      print $@->[1];  # error message
    }
  }

=head3 query_methods

  $service->query_methods();

Define a method which is called by the peer process.

=head2 Server side

=head3 start

  $service->start;

Initialize the connection port and wait for the client connection.
This method starts the event loop and blocks the control.

=head2 Client side

=head3 client_start

  $service->client_start;

Establish the connection to the server.
If connection failed, it will die.

=head3 stop

  $service->stop;

Shutdown the connection.


=head2 Utilities

=head3 to_sexp

Translate a Perl object into S-expression string.
In normal use, serializing and unserializing are applied automatically.

=head1 AUTHOR

Masashi Sakurai  C<< <m.sakurai@kiwanami.net> >>


=head1 LICENSE AND COPYRIGHT

Copyright (c) 2011, 2012 Masashi Sakurai C<< <m.sakurai@kiwanami.net> >>. All rights reserved.

This module is free software; you can redistribute it and/or
modify it under the same terms as Perl itself. See L<perlartistic>.


=head1 DISCLAIMER OF WARRANTY

BECAUSE THIS SOFTWARE IS LICENSED FREE OF CHARGE, THERE IS NO WARRANTY
FOR THE SOFTWARE, TO THE EXTENT PERMITTED BY APPLICABLE LAW. EXCEPT WHEN
OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER PARTIES
PROVIDE THE SOFTWARE "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER
EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE
ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE SOFTWARE IS WITH
YOU. SHOULD THE SOFTWARE PROVE DEFECTIVE, YOU ASSUME THE COST OF ALL
NECESSARY SERVICING, REPAIR, OR CORRECTION.

IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MAY MODIFY AND/OR
REDISTRIBUTE THE SOFTWARE AS PERMITTED BY THE ABOVE LICENSE, BE
LIABLE TO YOU FOR DAMAGES, INCLUDING ANY GENERAL, SPECIAL, INCIDENTAL,
OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OR INABILITY TO USE
THE SOFTWARE (INCLUDING BUT NOT LIMITED TO LOSS OF DATA OR DATA BEING
RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD PARTIES OR A
FAILURE OF THE SOFTWARE TO OPERATE WITH ANY OTHER SOFTWARE), EVEN IF
SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF
SUCH DAMAGES.
