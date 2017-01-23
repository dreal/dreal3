#!/usr/bin/env perl
#
# Call like this:
# ./prep_data.perl data/PROB-GOING-DOWNTOWN-LOW-FUEL-DISTRACTED-DRIVER_bjuxfo57-tmp

use strict;
use warnings;

use FindBin;
use Getopt::Long;
use JSON;

# ------------------------------------------------------------
# Global Variables

# Set to enable verbose (debugging) output.
my $verbose = 0;

my $output_filename = $FindBin::Bin . "/data.json";

# ------------------------------------------------------------
# Parse Arguments

GetOptions('v|verbose'          => \$verbose,
           'o|output=s'         => \$output_filename,
          ) or
  die ("Error parsing arguments.");

# Ensure that we have something to process.
(1 == scalar(@ARGV)) or
  die ("Need an argument specifying what to process.");

# ------------------------------------------------------------
# Main script

# Get the input filenames.
my $input_basename = shift(@ARGV);
my ($drh_filename, $json_filename) =
  find_input_files($input_basename);

# Read the JSON data first. We'll add to this.
print("Reading ODE and mode data from:\n");
print("  $json_filename\n");

my $data_ref = read_json_data($json_filename);
summarize_data($data_ref);

# If we have a model file, parse it.
if (defined($drh_filename)) {
  print("Parsing model data from:\n");
  print("  $drh_filename\n");
  # Parse the model data and put it in the $data_ref object.
  my $drh_ref = parse_drh_file($drh_filename);
  $data_ref->{drh} = $drh_ref;
}
else {
  # Should this be a warning?
  print("Did not find a .drh file, skipping model parsing.\n");
}

# Write the $data_ref to the destination location.
write_data($data_ref, $output_filename);

exit (0);

# End of main script
# ------------------------------------------------------------
# Subroutines

sub find_input_files {
  my $basename = shift();

  my $drh_pattern = "$basename*.drh";
  my @drh_matches = glob($drh_pattern);
  if (1 < scalar(@drh_matches)) {
    die ("Found multiple DRH files for: $basename");
  }
  # This will be the single filename or undef. We can proceed without
  # the model.
  my $drh_filename = shift(@drh_matches);

  my $json_pattern = "$basename*.smt2.json";
  my @json_matches = glob($json_pattern);
  if (1 < scalar(@json_matches)) {
    die ("Found multiple JSON files for: $json_pattern");
  }
  elsif (1 > scalar(@json_matches)) {
    die ("Did not find any JSON files for: $json_pattern");
  }
  # This will be the one single filename. We must have the JSON file
  # to proceed at all.
  my $json_filename = shift(@json_matches);

  return ($drh_filename, $json_filename);
}

sub read_json_data {
  my $filename = shift();

  # Read the config file contents.
  my $json_text = "";
  open (my $fh, "<", $filename) or
    die ("Unable to open JSON file: $filename");
  while (my $line = <$fh>) {
    chomp($line);
    # Remove comment-like things.
    $line =~ s/^\s*(?:#|\/\/|;).*//;
    $json_text .= $line;
  }

  # Turn it into an object.
  my $json = JSON->new();
  my $data_ref = $json->decode($json_text);

  return $data_ref;
}

sub summarize_data {
  my $data_ref = shift();

  print("  contains traces?   ... ");
  if ($data_ref->{traces}) {
    print("yes\n");
  }
  else {
    print("no\n");
  }
  print("  contains modes?    ... ");
  if ($data_ref->{modes}) {
    print("yes\n");
  }
  else {
    print("no\n");
  }
}

sub parse_drh_file {
  my $drh_filename = shift();

  open (my $in_fh, "<", $drh_filename) or
    die ("Unable to open drh file: $drh_filename");

  # This tracks the state of the parser. It is passed into each
  # parsing function so that the function can update the state.
  my $state_ref =
    { drh => {},
      component => undef,
      mode => undef,
      transition => undef,
    };

  while (my $line = <$in_fh>) {
    parse_line($line, $state_ref);
  }

  return $state_ref->{drh};
}

sub parse_line {
  my $line = shift();
  my $state_ref = shift();

  if (parse_component($line, $state_ref)) {
    $state_ref->{mode} = undef;
    $state_ref->{transition} = undef;
  }
  elsif (parse_mode_label($line, $state_ref) or
         parse_mode($line, $state_ref)) {
    $state_ref->{transition} = undef;
  }
  elsif (parse_transition_label($line, $state_ref) or
         parse_transition($line, $state_ref)) {
  }
}

sub parse_component {
  my $line = shift();
  my $state_ref = shift();

  ($line =~ /\(component (\S+);/) or
    return 0;

  my $component_name = $1;
  $verbose and
    print("  component: $component_name\n");

  # Store a new component.
  my $component_ref =
    { modes => {} };

  $state_ref->{drh}->{$component_name} = $component_ref;
  $state_ref->{component} = $component_ref;
  $state_ref->{mode} = undef;
  $state_ref->{transition} = undef;

  return 1;
}

sub parse_mode_label {
  my $line = shift();
  my $state_ref = shift();

  # This will only be assigned if we find a mode label. If we do, we
  # should create a new mode for it.
  my $mode_ref;

  if ($line =~ /#<(STATE\s+.+?):\s+#<FEATURE-SET\s+\((.+)\)>>/) {
    my $state_label = $1;
    my $state_features = $2;

    $mode_ref =
      { label => $state_label,
        features => $state_features,
      };
  }
  elsif ($line =~ /\/\*\s+(:\S+)\s+\*\//) {
    my $keyword = $1;
    $mode_ref = { label => $keyword, };
  }

  if (defined($mode_ref)) {
    # Add an empty array to hold the transitions.
    $mode_ref->{transitions} = [];
    # Store the mode for later.
    $state_ref->{mode} = $mode_ref;
    return 1;
  }
  return 0;
}

sub parse_mode {
  my $line = shift();
  my $state_ref = shift();

  ($line =~ /\(mode (\S+);/) or
    return 0;

  # Add the mode information to the component.
  my $mode_name = $1;
  $verbose and
    print("    mode: $mode_name\n");

  # If we don't have any mode details, create one now.
  if (not defined($state_ref->{mode})) {
    $state_ref->{mode} = { transitions => [], };
  }
  my $mode_ref = $state_ref->{mode};

  # Add the mode to the component.
  my $modes_ref = $state_ref->{component}->{modes};

  # If this mode was already stored, we must not have found any label
  # information. Just create a new mode before continuing so that we
  # don't pollute the old one.
  for my $stored_mode_ref (values(%{$modes_ref})) {
    if ($stored_mode_ref == $mode_ref) {
      $mode_ref = { transitions => [], };
    }
  }

  $modes_ref->{$mode_name} = $mode_ref;
  $state_ref->{mode} = $mode_ref;

  # For debugging purposes, go ahead and print any label or feature
  # information we had for this mode.
  if (defined($mode_ref->{label})) {
    $verbose and
      print("     label: " . $mode_ref->{label} . "\n");
  }
  if (defined($mode_ref->{features})) {
    $verbose and
      print("     features: " . $mode_ref->{features} . "\n");
  }

  return 1;
}

sub parse_transition_label {
  my $line = shift();
  my $state_ref = shift();

  # This will only be assigned if we find a transition label. If we
  # do, we should create a new transition for it.
  my $transition_ref;

  if ($line  =~ /#<(\S*COMPONENT-\S*TRANSITION)\s+(.+?)\s*>/) {
    my $transition_type = $1;
    my $transition_name = $2;
    $transition_ref =
      { type => $transition_type,
        name => $transition_name,
      };
  }

  if (defined($transition_ref)) {

    # If we have transition information that wasn't recorded, we probably parsed something wrong.
    if (defined($state_ref->{transition})) {
      die ("Dang. We found a transition label, but the old one wasn't recorded.");
    }

    # Store this transition information.
    $state_ref->{transition} = $transition_ref;

    return 1;
  }
  return 0;
}

sub parse_transition {
  my $line = shift();
  my $state_ref = shift();

  ($line =~ /^\s*\@(\S+)\s+(.+);/) or
    return 0;

  my $dest_mode_name = $1;
  # The condition is almost (but not) always "true". We don't bother
  # recording it here.
  my $condition = $2;

  my $transition_ref = $state_ref->{transition};
  defined($transition_ref) or
    die("Found destination mode name ($dest_mode_name), but never parsed transition info.");

  $verbose and
    print("      $transition_ref->{name} -> $dest_mode_name\n");
  $transition_ref->{dest_mode} = $dest_mode_name;

  my $mode_ref = $state_ref->{mode};
  defined($mode_ref) or
    die("Found transition to record, but there's no mode.");

  my $transitions_ref = $mode_ref->{transitions};
  defined($transitions_ref) or
    die("Found transition to record, but mode doesn't have a transitions array.");

  # Finally, add the transition to the list.
  push(@{$transitions_ref}, $transition_ref);

  # And stop recording things for this transition.
  $state_ref->{transition} = undef;

  return 1;
}

sub write_data {
  my $data_ref = shift();
  my $output_filename = shift();

  open (my $out_fh, ">", $output_filename) or
    die ("Unable to open output file: $output_filename");

  my $json = JSON->new()->pretty(1);
  print($out_fh $json->encode($data_ref));

  print("Writing data to: $output_filename\n");
  print("  done\n");
}

