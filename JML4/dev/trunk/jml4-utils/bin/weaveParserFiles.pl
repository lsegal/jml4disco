#!/usr/bin/perl
#=============================================================================
#
# weaveParserFiles.pl
#
# $Id$
#
# Copyright (C) 2007, DSRG (dsrg.org)
#
#=============================================================================

$^W = 1; # equivalent to using the -w command-line flag under UNIX.

use strict;
use warnings;
use diagnostics;
use Getopt::Std;
use FileHandle;
use File::Copy;
use English;

#------------------------------------------------------------------------------
# Global var decl

my $gProgNm    = "weaveParserFiles.pl";			# program name
my $gDbgTr     = 0;
my $gVerbose   = 0;
my ($gVersion) = '$Revision: 1.1 $' =~ /(\d+\.\d+)/;
my $gProgRslt  = 1;

my $gBuildDir = 'BUILD-DIR-HAS-NOT-BEEN-SET';
my $grammarDir  = $gBuildDir;
my $parserDir   = $gBuildDir;

my $parserBasicInfoBlankLineCount = 0;

#------------------------------------------------------------------------------
# Forward declarations

sub cmdLine();
sub main();
sub HelpAndExit(;$);
sub Usage();
sub getFileHandle($$);

sub doCmd($$$);
sub checkForDir($$);
sub checkWorkSpaceDir($);
# sub MRRCNR($);

#------------------------------------------------------------------------------
# Prog body

eval {
    main();
};
die "FATAL ERROR: $EVAL_ERROR" if $EVAL_ERROR;
exit 0;

#------------------------------------------------------------------------------
# Subroutines
#------------------------------------------------------------------------------

sub main() {
    autoflush STDOUT, 1;
    autoflush STDERR, 1;
    my $args = cmdLine();

    HelpAndExit() if !checkForDir("Build directory", $gBuildDir);

    $grammarDir  = $gBuildDir;
    $parserDir   = $gBuildDir;

    my $rhInfo;

    # update JmlParserHelper.java
    print STDOUT "Updating JmlParserHelper.java (parser dir) ...";
    $rhInfo = {
	# source  => $parserDir . "/Parser.java",
	source  => $parserDir . "/JmlParserHelper.java",
	srcpat  => ['^protected\svoid\sconsumeRule\(int', '^\}\s*$'],
	addpatln=> 0,
	replace => $grammarDir . "/JavaAction.java",
	ssrpat  => ['(^protected\svoid\sconsumeRule\(int.*)$', '1'],
	ssrpre  => '',
	esrpat  => ['^(\})\s*$', ' '],
	addpats => undef,
	arpats  => ['(.*)','1','fixJmlParserHelperLines'], 
    };
    &MRRCNR($rhInfo);
    print STDOUT " done!\n";

    #update ParserBasicInformation.java
    print STDOUT "Updating ParserBasicInformation.java (parser dir) ...";
    $rhInfo = {
	source  => $parserDir . "/ParserBasicInformation.java",
	srcpat  => ['^public\sinterface\sParserBasicInformation', '^\}\s*$'],
	addpatln=> 1,
	replace => $grammarDir . "/javadef.java",
	ssrpat  => ['^\{(\s*)$', '1'],
	ssrpre  => '',
	esrpat  => ['^(\})\;\s*$', ''],
	addpats => undef,
	arpats  => ['(.*)','1','fixParserBasicInfo'],
    };
    &MRRCNR($rhInfo);
    print STDOUT " done!\n";

    #update TerminalTokens.java
    print STDOUT "Updating TerminalTokens.java (parser dir) ...";
    $rhInfo = {
	source  => $parserDir . "/TerminalTokens.java",
	srcpat  => ['^\s*int\sTokenNameIdentifier', '^\}\s*$'],
	addpatln=> 0,
	replace => $grammarDir . "/javasym.java",
	ssrpat  => ['^\s*(TokenNameIdentifier.*)$', '1' ],
	ssrpre  => "\tint ",
	esrpat  => ['^(\})\s*$', ''],
	arpats  => ['(.*)','1','fixTerminalTokens'],
	# arpats  => ['\$(\w{3,5})','1','toupper'],
    };
    &MRRCNR($rhInfo);
    print STDOUT " done!\n";
}

##
# MRRCNR - Move Read Read Cut N Replace
#
sub MRRCNR($) {
    my ($rhInfo) = @ARG;
    defined($rhInfo) || die "undefined hash!";
    my ($s,$m,$h,$d,$mo,$y) = (localtime)[0..5];
    my $prevFile = sprintf('%s.%d%02d%02d%02d%02d%02d',
			   $rhInfo->{source},(1900+$y),($mo+1),$d,$h,$m,$s);
    my $replacmentLineCount = 0;
    # `mv $sourceFile $prevFile`;
    move($rhInfo->{source}, $prevFile) || die "move - $OS_ERROR";
    open(INSRC, "<$prevFile") or die $OS_ERROR . " - $prevFile";
    open(OUT, ">$rhInfo->{source}") or die $OS_ERROR . " - $rhInfo->{source}";
    my $startSrcFound=0;
    # Iterate through the file
    while(my $line = <INSRC>) {
	chomp($line);
	printf STDERR "READING: %s: ", $line if $gDbgTr;
	# Starting pattern is found.
	if($line =~ /$rhInfo->{srcpat}->[0]/) {
	    printf STDERR "--> FOUND START PATTERN" if $gDbgTr;
	    $startSrcFound = 1;
	    if($rhInfo->{addpatln}) {
		print OUT $line . "\n";
	    }
	    next;
	}
	# Ending pattern is found.
	if($line =~ /$rhInfo->{srcpat}->[1]/) {
	    if($startSrcFound) { # time to copy the other file
		open(INRPL, "<$rhInfo->{replace}") 
		    || die $OS_ERROR . " - $rhInfo->{replace}";
		my $startRplFound=0;
		while(my $line = <INRPL>) { # copy the rest
		    chomp($line);
		    no strict "refs";
		    if($line =~ s/$rhInfo->{ssrpat}->[0]/${$rhInfo->{ssrpat}->[1]}/) {
			$line = $rhInfo->{ssrpre} . $line if($rhInfo->{ssrpre});
			print OUT $line . "\n";
			$replacmentLineCount++;
			$startRplFound = 1;
			next;
		    }
		    if($line =~ s/$rhInfo->{esrpat}->[0]/$1$rhInfo->{esrpat}->[1]/) {
			print OUT $line . "\n";
			$replacmentLineCount++;
			$startRplFound = 0;
			next;
		    }
		    if($startRplFound) {
			if(defined($rhInfo->{arpats})) {
			    my $var = $rhInfo->{arpats}->[1];
			    my $subUC = $rhInfo->{arpats}->[2];
			    $line =~ s/$rhInfo->{arpats}->[0]/&{$subUC}(${$var})/e;
			    next if $line =~ /DSRG_SKIP_THIS_LINE/;
			}
			print OUT $line . "\n";
			$replacmentLineCount++;
		    }
		}
		close(INRPL);
	    } else {
		print OUT $line . "\n";
	    }
	    $startSrcFound = 0;
	    next;
	}
	# Copy the content that is not to be replaced.
	if($startSrcFound) {
	    # skip this part - will be replaced when the end is found.
	    printf STDERR "--> LINE SKIPPED\n" if $gDbgTr;
	} else {
	    printf STDERR "--> to outflie\n" if $gDbgTr;
	    print OUT $line . "\n";
	}
    }
    if($replacmentLineCount == 0) {
	die "File: '$rhInfo->{source}'. Something has gone wrong. No lines were replaced.\n" .
	    "\tThis is probably because pattern matching failed to find the location in\n" .
	    "\tthe file where the replacement was to occur. See the script \n" .
	    "\t$0 for start and end patterns expected to be found in this file.\n";
    }
    close(INSRC);
    close(OUT);
}

sub fixJmlParserHelperLines($) {
    my ($line)=@ARG;

    $line =~ s/^(\s+)(consume|ignoreExpressionAssignment)/$1_this.$2/;
    $line =~ s/(THIS|SUPER)_CALL/Parser.$1_CALL/g;
    return $line;
}

sub fixTerminalTokens($) {
    my ($line)=@ARG;

    # Map TokenName$abc -> TokenNameABC
    if(my ($part) = $line =~ /TokenName\$(\w*)/) {
	my $ucPart = uc($part);
	$line =~ s/TokenName\$(\w)*/TokenName$ucPart/;
    }
    $line =~ s/^\s*(\w*\s*=)/\t\t$1/;
    return $line;
}

sub fixParserBasicInfo($) {
    my ($line)=@ARG;

    if(!$line && $parserBasicInfoBlankLineCount == 0) {
	$parserBasicInfoBlankLineCount++;
	return "DSRG_SKIP_THIS_LINE";
    }
    $line =~ s/\s*public final static int/DSRG_SKIP_THIS_LINE/;
    $line =~ s/^\s*(ERROR_SYMBOL)\s*=/\tint $1 =/;
    $line =~ s/^\s*(\w*)\s*=/\t\t$1 =/;
    return $line;
}

sub toupper {
    my ($str)=@ARG;
    return uc($str);
}

sub doCmd($$$) {
    my ($what, $dir, $cmd) = @_;

    printf STDOUT "$what %s...", ($gVerbose ? $cmd : '');
    my $out = `cd "$dir"; $cmd`;
    die "$cmd.\n ErrorNo: $CHILD_ERROR" if $CHILD_ERROR;
    print STDOUT "\n$out\n" if $out;
    print STDOUT " done!\n";
}

sub checkForDir($$) {
    my ($dirName, $dir) = @_;

    if(! -e $dir) {
	printf STDERR "$dirName '$dir' does not exist\n";
	return 0;
    } elsif (! -d $dir) {
	printf STDERR "$dirName '$dir' exists but is not a directory!\n";
	return 0;
    }
    return 1;
}

#------------------------------------------------------------------------------
# General utils

sub readEntireFile($) {
    my ($fileName) = @_;

    # There is a more efficient way to do this ... but it escapes me right now.
    my $fh = getFileHandle($fileName, '<') || die;
    my @lines = <$fh>;
    return join(@lines, '');
}

sub getFileHandle($$)
{
    my ($path, $mode) = @_;

    my $fh = new FileHandle "$mode $path";
    if(!$fh) {
	printf("getFileHandle: could not open file '$path'.\n");
	return;
    }
    return $fh;
}

sub cmdLine()
{
    # Process command line flags
    my %opt;

    if(!getopts('d:hvZ:',\%opt)) {
	HelpAndExit();
    } elsif($opt{h}) {
	Usage();
	exit 0;
    }

    if(defined $opt{d}) {
	$gBuildDir = $opt{d};
    } else {
	HelpAndExit("Mandatory command line argument -d is missing.");
    }

    $gVerbose = defined $opt{v};
    $gDbgTr ||= $opt{Z};

    # Ensure that there are no other arguments lingering around.
    HelpAndExit('extra arguments on the command line: "'.
		join(' ', @ARGV) . '".') if @ARGV;
    return \%opt;
}

sub HelpAndExit(;$)
{
    my ($msg) = @_;
    printf STDERR "$gProgNm: %s\n", $msg if $msg;
    printf STDERR "$gProgNm: use -h flag for help.\n";
    exit $gProgRslt || 1;
}

sub Usage()
{
    print <<EndOfUsageText;
Usage: $gProgNm [options] [files]
    e.g.
    $gProgNm -d <build-dir-containing-files>

    This script is part of a system used to rebuild the JDT Parser from the
    bits and pieces created by the JikesPG. This file weaves together some of
    the parser .java files from JikesPG output and the original versions of
    the Java files.

  Options:
    -d <path>  Path to build dir.  The dir should contain the files to be operated on
               and it will also be used as a scratch working dir.
    -h         print this help information.
    -v         verbose (quiet by default). [not currently active]
    -Z <n>     set debugging trace to level <n>. [not currently active]

[Script version $gVersion]
EndOfUsageText
}

#------------------------------------------------------------------------------
# End of file $RCSfile: weaveParserFiles.pl,v $
