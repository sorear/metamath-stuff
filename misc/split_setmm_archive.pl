#!/usr/bin/perl

use strict; use warnings;

use Text::CleanFragment;
use Time::ParseDate;
use File::Slurper qw( read_text read_dir );
use HTML::Entities;

my %breaks = ( '######' => 1, '#*#*#*' => 2, '=-=-=-' => 3 );

if (@ARGV == 2) {
    my ($file, $name) = @ARGV;
    my $time = parsedate(($name =~ /([0-9]{4}-[0-9]{2}-[0-9]{2})/) ? $1 : '1990-01-01', GMT => 1);
    scrape($time, $time, $name, $file, 1);
}
else {
    my @versions = grep { /set\.mm/ } read_dir(".");

    my %mtime;
    my %offtime;
    for (@versions) {
        $offtime{$_} = parsedate(/([0-9]{4}-[0-9]{2}-[0-9]{2})/ ? $1 : '1990-01-01', GMT => 1);
        $mtime{$_} = (stat($_))[9];
    }

    @versions = sort { ($offtime{$a} <=> $offtime{$b}) || ($mtime{$a} <=> $mtime{$b}) } @versions;

    for my $v (@versions) {
        my $mtime = $mtime{$v};
        my $offtime = $offtime{$v};
        scrape($mtime, $offtime, $v, $v);
    }
}

sub scrape {
    my ($mtime, $offtime, $v, $file, $continue) = @_;
    print "progress ** $v $mtime $offtime\n";

    my $text = read_text($file);
    $text =~ s/\r//g;
    my @lines = split /^/m, $text;

    my @segments = ( { name => 'FRONT', level => 0, lines => [] } );
    my @used_levels;

    while (@lines) {
        # search forward for the next section break or EOF

        my $i = 0;
        while ($i < @lines) {
            my $b = $breaks{substr($lines[$i],0,6)};

            if ($b) {
                # a true section break must have a comment open on the line before
                # nested comments still count
                if ($i > 0 && $lines[$i-1] =~ /[\$\@]\(/) {
                    last;
                }
                else {
                    $segments[-1]{false} = 1;
                    $i++;
                }
            }
            else {
                $i++;
            }
        }

        if ($i >= @lines) {
            # EOF
            push @{$segments[-1]{lines}}, splice(@lines);
            last;
        }

        # we found a segment mark.  identify the ends of the segment "header" and its name
        my $level = $breaks{substr($lines[$i],0,6)};
        $used_levels[$level] = 1;

        # name is from the first line after the segment mark with at least one wordchar
        my $nline = $i;
        while ($nline < @lines && $lines[$nline] !~ /\w/) { $nline++; }
        my $name = ($nline >= @lines) ? 'Malformed' : $lines[$nline];
        $name =~ s/\A\s+|\s+\z//g;

        my $first = $i;
        while ($first > 0 && $lines[$first-1] =~ /\S/) { $first--; }

        # copy out everything before the section header, trying to include comment markers and mmj2 metadata in the "header"
        push @{$segments[-1]{lines}}, splice(@lines,0,$first);
        $i -= $first;

        my $last = $i+1;
        while ($last < @lines && $lines[$last] =~ /\S/) { $last++; }

        # create a new header
        push @segments, { name => $name, level => $level, lines => [] };

        # force the rest of the header into the new section so that the trailing mark is not intepreted as a section mark
        push @{$segments[-1]{lines}}, splice(@lines,0,$last);
    }

    if (!@used_levels) { $used_levels[1] = 1; }
    my $nlevel = 0;
    for (@used_levels) { $_ = $nlevel++ if $_ }

    my %filedata;

    $filedata{README} = <<'README' ;
This repository contains old versions of the "set.mm" Metamath database for
first-order set theory.  Each revision corresponds to an archived version of
set.mm.  Files have been split for more efficient storage and easier perusal.
If you need to reconstruct a complete set.mm file, use:

cat $(cat MANIFEST)

or the local equivalent.  Note that you cannot assume old versions of set.mm
can be loaded unmodified in current versions of metamath.

For the current version of set.mm and extensive supplemental information, see:

http://us.metamath.org/mpegif/mmset.html
README

    $filedata{MANIFEST} = '';

    my @path = ( ('TOP') x $nlevel );

    for my $s (@segments) {
        printf "progress %4d %s%d   %s\n", 0+@{$s->{lines}}, $s->{false} ? '*' : ' ', $s->{level}, $s->{name};

        if ($s->{level}) {
            my $level = $used_levels[$s->{level}];
            $path[$level] = clean_fragment(decode_entities($s->{name})); #Mathbox_for_Fr_eacute_d_eacute_ric_Lin_eacute
            $path[$_] = 'TOP' for $level + 1 .. $nlevel - 1;
        }

        my $name = join '/', @path;
        my $disam = 1;

        while (exists $filedata{$name}) { $name = join('/',@path) . '-' . $disam++; }

        $filedata{$name} = join '', @{ $s->{lines} };
        $filedata{MANIFEST} .= "$name\n";
    }

    print "commit refs/heads/master\n";
    print "committer <unknown> $mtime +0000\n";
    my $cmsg = "extracted revision from file $v\n";
    print "data ",length($cmsg),"\n",$cmsg,"\n";
    print "from refs/heads/master^0\n";
    print "deleteall\n";
    for my $p (sort keys %filedata) {
        print "M 644 inline $p\ndata ",length($filedata{$p}),"\n",$filedata{$p},"\n";
    }
}
