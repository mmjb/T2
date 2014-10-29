#!/usr/bin/perl
use warnings;
use strict;
use File::Find;

my ($DIR, @trash) = @ARGV;

if (!$DIR) {
	die "Usage: $0 DIRECTORY";
}
chdir($DIR);

our %results;
find({ wanted => \&process_file, follow => 1, no_chdir => 1 }, '.' );

open (RESULTS, '>',  'RESULT.csv') or die "Can't write to RESULT.csv: $!";
for my $ex_name (sort keys %results) {
	my ($res, $time) = ($results{$ex_name}->{'result'}, $results{$ex_name}->{'time'});
	printf RESULTS "%s,%s,%.3f\n", $ex_name, $res, $time;
}
close (RESULTS);

exit;

sub process_file {
	#Only look at .out files:
	return if ($_ !~ /.out$/);
	
	#The stuff we wanna know:
	my $name = $File::Find::name;
	$name =~ s/.out$//;
	$name =~ s!^./!!;
	my $res = "ERROR";
	my $time = 0;
	open (DATA, '<', $File::Find::name) or die "Can't read $File::Find::name: $!";
	my $after_first_line = 0;
	while (<DATA>) {
		$_ =~ s/\r?\n?$//;
		if ($_ !~ /^wlimit>/ && !$after_first_line) {
			##### AProVE result:
			if ($_ eq "YES") {
				$res = "SAFE+TERMINATING";
			} elsif ($_ eq "NO") {
				$res = "SAFE+NONTERMINATING";
			} elsif ($_ eq "MAYBE") {
				$res = "UNKNOWN";
			} elsif ($_ eq "KILLED" || $_ eq "TIMEOUT") {
				$res = "TIMEOUT";
			}
			$after_first_line = 1;
		}

		##### wlimit results:
		if ($_ =~ /Status: *([0-9]+)/) {
			if ($1 == 1) {
				$res = "TIMEOUT";
			} elsif ($1 == 4) {
				$res = "MEMOUT";
			}

		##### wlimit time (in ms):
		} elsif ($_ =~ /TotalWallClockTime: ([0-9.]+)/) {
			$time = $1/1000;
		}
	}
	close (DATA);

	$results{$name} = { time => $time, result => $res };
}
