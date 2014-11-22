#!/usr/bin/perl
use strict; use warnings;
use File::Slurp 'read_file', 'write_file';

my $name = "Stefan O'Rear";
my $smm = read_file 'sorear.mm';

my @parts = split /(\$\( .*? \$\))/s, $smm, -1;

for my $i ( 0 .. $#parts - 2 ) {
    my ($label) = $parts[$i+1] =~ /^\s*(\S+)\s+\$p\s/ or next;
    my ($date) = $parts[$i+2] =~ /\$\( \[([0-9a-zA-z-]+)\] \$\)/ or next;
    if ($parts[$i] =~ /^\$\(/ && $parts[$i] !~ /Contributed\s*by/ && $parts[$i] !~ /Lemma for/ && $label !~ /lem\d*$/) {
        $parts[$i] =~ s/ \$\)/ (Contributed by $name, $date.) \$\)/;
    }
}

write_file 'sorear.mm', join '', @parts;

print ">> sorear.mm rewritten.  use /REWRAP to ensure consistent formatting. <<\n";
