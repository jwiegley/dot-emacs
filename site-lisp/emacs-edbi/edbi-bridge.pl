#!/usr/bin/perl

use strict;
use RPC::EPC::Service;
use Data::Dumper;
use DBI;

our $dbh = undef;
our $sth = undef;

sub edbi_connect {
  my ($args) = @_;
  my ($data_source,$username,$auth) = @$args;
  if ($dbh) {
    eval {
      $dbh->disconnect();
    }
  }
  our $dbh = DBI->connect($data_source, $username, $auth);
  return $dbh->get_info(18);
}

sub edbi_do {
  return undef unless $dbh;
  my ($args) = @_;
  my ($sql, $params) = @$args;
  my $rows = $dbh->do($sql, undef, @$params);
  return $rows;
}

sub edbi_select_all {
  return undef unless $dbh;
  my ($args) = @_;
  my ($sql, $params) = @$args;
  my $rows = $dbh->selectall_arrayref($sql, undef, @$params);  return $rows;
}

sub edbi_prepare {
  return undef unless $dbh;
  $sth->finish() if $sth;
  my ($sql) = @_;
  our $sth = $dbh->prepare($sql) or return undef;
  return 'sth';
}

sub edbi_execute {
  return undef unless $sth;
  my ($params) = @_;
  return $sth->execute(@$params) or return undef;
}

sub edbi_fetch_columns {
  return undef unless $sth;
  return $sth->{NAME};
}

sub edbi_fetch {
  return undef unless $sth;
  my ($num) = @_;
  if ($num eq undef) {
    return $sth->fetchall_arrayref();
  } else {
    my $ret = [];
    for (my $i = 0; $i < $num; $i++) {
      my $row = $sth->fetchrow_arrayref();
      last if $row eq undef;
      push @$ret, $row;
    }
    return $ret;
  }
}

sub edbi_auto_commit {
  return undef unless $dbh;
  my ($flag) = @_;
  if ($flag eq "true") {
    $dbh->{AutoCommit} = 1;
    return 1;
  } else {
    $dbh->{AutoCommit} = 0;
    return 0;
  }
}

sub edbi_commit {
  return undef unless $dbh;
  $dbh->commit();
  return 1;
}


sub edbi_rollback {
  return undef unless $dbh;
  $dbh->rollback();
  return 1;
}

sub edbi_disconnect {
  return undef unless $dbh;
  $dbh->disconnect();
  return 1;
}

sub edbi_status {
  return undef unless $dbh;
  return [$dbh->err, $dbh->errstr, $dbh->state];
}

sub edbi_type_info_all {
  return undef unless $dbh;
  my $ret = $dbh->type_info_all;
  print STDERR Dumper $ret;
  return $dbh->type_info_all;
}

sub edbi_table_info {
  return undef unless $dbh;
  eval {
    $sth->finish() if $sth;
  };
  my ($args) = @_;
  my ($catalog, $schema, $table, $type) = @$args;
  $sth = $dbh->table_info( $catalog, $schema, $table, $type );
  return [$sth->{NAME}, $sth->fetchall_arrayref()];
}

sub edbi_column_info {
  return undef unless $dbh;
  eval {
    $sth->finish() if $sth;
  };
  my ($args) = @_;
  my ($catalog, $schema, $table, $column) = @$args;
  $sth = $dbh->column_info( $catalog, $schema, $table, $column );
  return [[],[]] unless $sth;
  return [$sth->{NAME}, $sth->fetchall_arrayref()];
}

sub edbi_primary_key_info {
  return undef unless $dbh;
  eval {
    $sth->finish() if $sth;
  };
  my ($args) = @_;
  my ($catalog, $schema, $table) = @$args;
  $sth = $dbh->primary_key_info( $catalog, $schema, $table );
  return undef unless $sth;
  return [$sth->{NAME}, $sth->fetchall_arrayref()];
}

sub edbi_foreign_key_info {
  return undef unless $dbh;
  eval {
    $sth->finish() if $sth;
  };
  my ($args) = @_;
  my ($pkcatalog, $pkschema, $pktable, $fkcatalog, $fkschema, $fktable) = @$args;
  $sth = $dbh->foreign_key_info( $pkcatalog, $pkschema, $pktable,
                                 $fkcatalog, $fkschema, $fktable );
  return undef unless $sth;
  return [$sth->{NAME}, $sth->fetchall_arrayref()];
}

sub main {
  my $methods =
    {
     'connect' => [\&edbi_connect,"data_source, username, auth", ""],
     'do' => [\&edbi_do, "sql, params", ""],
     'select-all' => [\&edbi_select_all, "sql, params", ""],
     'prepare' => [\&edbi_prepare, "sql", ""],
     'execute' => [\&edbi_execute, "params", ""],
     'fetch-columns' => [\&edbi_fetch_columns, "", ""],
     'fetch' => [\&edbi_fetch, "[number]", ""],
     'auto-commit' => [\&edbi_auto_commit, "false/true", ""],
     'commit' => [\&edbi_commit, "", ""],
     'rollback' => [\&edbi_rollback, "", ""],
     'disconnect' => [\&edbi_disconnect, "", ""],
     'status' => [\&edbi_status, "", ""],
     'type-info-all' => [\&edbi_type_info_all, "", ""],
     'table-info' => [\&edbi_table_info, "catalog, schema, table, type", ""],
     'column-info' => [\&edbi_column_info, "catalog, schema, table, column", ""],
     'primary-key-info' => [\&edbi_primary_key_info, "catalog, schema, table", ""],
     'foreign-key-info' => [\&edbi_foreign_key_info, "pk_catalog, pk_schema, pk_table, fk_catalog, fk_schema, fk_table", ""],
    };
    my $server = RPC::EPC::Service->new(0, $methods);
    $server->start;
}

main;

