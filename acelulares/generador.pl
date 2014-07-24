#!/usr/bin/perl
use strict;
use warnings;

package Automaton {
 sub new {
        my $class = shift;
        my $rule = [ reverse split //, sprintf "%08b", shift ];
        return bless { rule => $rule, cells => [ @_ ] }, $class;
 }
 sub next {
        my $this = shift;
        my @previous = @{$this->{cells}};
        $this->{cells} = [
         @{$this->{rule}}[
         map {
         4*$previous[($_ - 1) % @previous]
         + 2*$previous[$_]
         + $previous[($_ + 1) % @previous]
         } 0 .. @previous - 1
         ]
        ];
        return $this;
 }
 use overload
 q{""} => sub {
        my $this = shift;
        join '', map { $_ ? '#' : ' ' } @{$this->{cells}}
 };
}

my $rule=@ARGV[0]+0;
my $filename = @ARGV[1];
open(my $fh, '>', $filename) or die "Could not open file '$filename' $!";

my ($width, $height) = (500, 500);
my @a = map 0, 1 .. $width; $a[$width - 1] = 1;
my $a = Automaton->new($rule, @a);

print $fh "P1\n$width $height\n";
for (1 .. $height) {
 print $fh join ' ', @{$a->{cells}};
 print $fh "\n";
 $a->next;
}
system("qiv",$filename);
