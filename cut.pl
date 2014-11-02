#!/usr/bin/perl
use strict; use warnings;
use File::Slurp 'read_file', 'write_file';

my @status = grep { length } split /\0/, scalar qx{ git status -z };

my @lines = read_file $ARGV[0];

shift(@lines) while @lines >= 3 && $lines[2] !~ /Mathbox for Stefan O'Rear/;
pop(@lines) while @lines && $lines[-1] !~ /\$\( \(End of Stefan O'Rear's mathbox\.\) \$\)/;

unshift(@lines, "\$[ set_clean.mm \$]\n\n");

rename('sorear.mm','sorear.mm~'.time()) or die "cannot save mathbox backup: $!\n";
write_file('sorear.mm', \@lines);
