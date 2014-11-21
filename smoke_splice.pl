#!/usr/bin/perl
use strict; use warnings;
use File::Slurp 'read_file', 'write_file';

my $in = read_file $ARGV[0];
my $in2 = read_file 'sorear.mm';
my $in3 = read_file 'math_tokens.txt';

$in =~ s|/\* Mathbox of Stefan O'Rear \*/\n.*?\n\n|$in3|s;
$in2 =~ s|.*Mathbox for Stefan O'Rear.*?\$\)||s;
$in =~ s|Mathbox for Stefan O'Rear.*?\$\)\K.*?\$\( \(End of Stefan O'Rear's mathbox\.\) \$\)\n|$in2|s;

print $in;
