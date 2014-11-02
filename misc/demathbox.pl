# post-processes the output of ./metamath "SET W 300" "READ foo.mm" "V P *" "EXIT"

# ?Error on line 44 of file "dprm.mm" at statement 50305, label "elmapex1", type "$p":
#       vex eqtri co mapval ovex eqeltrri elovdm ) DEFHHEIZDIZGIJGKZABLCHLDEHHUIM
#                                         ^^^^^^
# This token is not the label of an assertion or optional hypothesis.

use strict;
use warnings;

my @lines = <STDIN>;

while (@lines >= 4) {
    if ($lines[0] !~ /^\?Error/ || $lines[3] !~ /assertion or optional hypothesis/) {
        shift @lines;
        next;
    }

    my ($label) = $lines[0] =~ /label "([^"]*)"/;
    my ($spaces, $carets) = $lines[2] =~ /( *)(\^*)/;

    my $error = substr($lines[1],length($spaces),length($carets));

    printf "%20s | %s\n", $label, $error;
    shift @lines;
}
