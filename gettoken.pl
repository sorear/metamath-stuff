#!/usr/bin/perl
use strict; use warnings;
use File::Slurp 'read_file', 'write_file';

my $in = read_file $ARGV[0];
my ($tok) = $in =~ m|(/\* Mathbox of Stefan O'Rear \*/\n.*?\n\n)|s;
write_file('math_tokens.txt', $tok);
