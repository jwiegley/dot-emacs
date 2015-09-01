
use warnings;
use strict;

use IO::Select qw();
use IO::Socket::INET qw();

my %config = (
    muse_emacs => '/usr/local/bin/emacs',
    muse_init => '/stuff/proj/personal-site/ikiwiki/muse-init.el',
    muse_shared_secret => 'foo',
);

my %MUSE_SERVER = ( host => 'localhost' );

main();
exit 0;

# Determine the emacs binary to use
sub locate_emacs {
    my $err = sub {
        die "Unable to find your emacs binary.\n",
          "  Set muse_emacs config to the right value.\n";
    };
    if ( $config{muse_emacs} ) {
        ( -x $config{muse_emacs} ) ? return $config{muse_emacs} : $err->();
    }
    else {
        my $emacs = `which emacs`;
        chomp $emacs;
        ( $emacs ) ? return $emacs : $err->();
    }
}

# Initialize connection to the Muse IPC server
sub start_muse_server {
    my $secret = $config{muse_shared_secret};
    my $init_port = $config{muse_init_port} || 0;
    my $ipc_port = $config{muse_ipc_port};

    # Perform sanity checks
    $config{muse_init} or die "Error: muse_init config option not defined.\n";

    # Start initialization server
    my $pserver = IO::Socket::INET->new(
        Proto => 'tcp',
        LocalAddr => 'localhost',
        LocalPort => $init_port,
        Listen => IO::Socket::INET::SOMAXCONN,
    ) or die "Error: Cannot begin initialization for the Muse IPC server.\n";
    $pserver->autoflush(1);
    $init_port = $pserver->sockport();
    my $select = IO::Select->new($pserver);

    # Start Emacs
    defined(my $pid = fork()) or die "Error: Unable to fork.\n";
    if ( $pid ) {
        $MUSE_SERVER{pid} = $pid;
    }
    else {
        exec locate_emacs(),
          qw( -q --no-site-file -batch -l ), $config{muse_init},
          qw( --eval ), "(muse-ikiwiki-start-server \"$init_port\"" .
          ( $ipc_port ? " \"$ipc_port\"" : '' ) . ")";
        die "Error: Unable to exec emacs.\n";
    }

    my $emacs_port = undef;

  SERVER:
    # Respond to clients
    while ( my @ready = $select->can_read() ) {
        for my $client (@ready) {
            if ($client == $pserver) {
                my $new = $pserver->accept();
                $select->add($new);
                next;
            }
            my $line = <$client>;
            chomp $line if defined $line;
            if ( defined $line && $line =~ m/^begin (.+)$/s &&
                   $1 eq $secret ) {
                print $client "ok\n";
                $line = <$client>;
                chomp $line if defined $line;
                if ( defined $line && $line =~ m/^port (.+)$/s ) {
                    $emacs_port = $1;
                }
                else {
                    print STDERR <<EOF;
Error: Invalid response while initializing Muse IPC server.
EOF
                }
                last SERVER;
            }
            print $client "nok\n" if $line;
            $select->remove($client);
            $client->close();
        }
    }
    $pserver->close();

    if ( $emacs_port ) {
        $MUSE_SERVER{port} = $emacs_port;
    }
    else {
        kill_muse_server();
    }
}

sub stop_muse_server {
    my ( $sock ) = @_;

    if ( $MUSE_SERVER{pid} ) {
        # Give Muse 3 seconds to stop, presuming that it has already
        # been sent the "done" command via stop_muse_server.
        local $SIG{ALRM} = sub {
            kill 9, $MUSE_SERVER{pid};
            die "Timeout";
        };
        eval {
            alarm 3;
            print $sock "done\n";
            $sock->close();
            waitpid($MUSE_SERVER{pid}, 0);
            alarm 0;
        };
        delete $MUSE_SERVER{pid};
    }
    else {
        print $sock "done\n";
        $sock->close();
    }
}

sub kill_muse_server {
    my @msgs = @_;

    kill 9, $MUSE_SERVER{pid} if $MUSE_SERVER{pid};
    die @msgs if @msgs;
}

sub ipc_expect_ok {
    my ( $sock, $err_msg ) = @_;
    $err_msg = "Error: Command did not succeed on Muse IPC server.\n";

    my $line = <$sock>;
    chomp $line;
    if ( $line ne 'ok' ) {
        $sock->close();
        kill_muse_server $err_msg;
    }
}

sub ipc_connect {
    my $secret = $config{muse_shared_secret};
    my $host = $MUSE_SERVER{host};
    my $port = $MUSE_SERVER{port};
    $host && $port
      or kill_muse_server "Error: No Muse IPC server is active.\n";

    # Start client connection
    my $sock = IO::Socket::INET->new(
        Proto => 'tcp',
        PeerAddr => $host,
        PeerPort => $port,
    ) or kill_muse_server "Error: Cannot connect to the Muse IPC server.\n";
    $sock->autoflush(1);

    # Authenticate
    print $sock "begin $secret\n";
    ipc_expect_ok $sock,
      "Error: Could not authenticate to the Muse IPC server.\n";

    return $sock;
}

sub test_name {
    my ( $sock ) = @_;

    print $sock "name foobar\n";
    ipc_expect_ok $sock,
      "Error: Could not set name of page on Muse IPC server.\n";
}

sub test_title {
    my ( $sock ) = @_;

    print $sock "title quux\n";
    ipc_expect_ok $sock,
      "Error: Could not set title of page on Muse IPC server.\n";
}

sub main {
    print "Starting Muse server ...\n";
    start_muse_server();

    print "Got port $MUSE_SERVER{port}.\n";
    my $sock = ipc_connect();
    test_name($sock);
    test_title($sock);

    print "Shutting down ...\n";
    stop_muse_server($sock);
    print "Done shutting down.\n";
}
