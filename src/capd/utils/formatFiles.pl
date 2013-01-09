#!/usr/bin/perl -w

my $oldLicenceFile = 'oldLicence.txt';
my $newLicenceFile = 'newLicence.txt';
my $directory = "..";
my %options;
my $allOptionsList = 'ldfbvr';
my $defaultOptionsList = '+'.$allOptionsList;

my $enter ="\r\n";

sub help{
print <<END_OF_HELP;
Usage: formatCAPD [+|-option1 [+|-option2 ...]] path
Format C++ code according to CAPD standards 

This is work in progress, options available in present version: 
  l  replace old licence text with the new one
  p  put licence text to files without licence
  d  correct symbol defined to dissable double inclusion of the same header file
      for file /include/capd/dynset/set.h it should be _CAPD_DYNSET_SET_H_
  f  correct file name in the \@file tag of Doxygen documentation
  b  backup files before proceeding
  v  verbose, display changes 
  r  process directories recursively
  a  all above
Default options: $defaultOptionsList 
END_OF_HELP
}


sub loadFile{
    my $name = $_[0];
    open(FILE, "<", $name);
    my @zawartosc = <FILE>;
    close FILE;
    return @zawartosc;
}

my @oldLicence = loadFile($oldLicenceFile);
my @newLicence = loadFile($newLicenceFile);


sub doxygenCorrectFileName{
  my @result;
  my $fileName = shift @_;
  if($fileName =~ /\/([^\/]+)$/){
    $fileName = $1;
  }
  foreach my $line (@_){
    if  ($line =~ /\s*\/\/\/\s*\@file\s*(\S*)/) {
      push @result, "/// \@file $fileName$enter";
      print "   change: Doxygen tag \@file $1 => $fileName\n" if(($options{v}) && ($1 ne $fileName));
    }else{
      push @result, $line;    
    }
  }
  return @result;
}

sub changeLicence {
  my @result;
  my $licenceLineNumber = 0;
  my @data= @_;
# in tmpLicence we store lines of old licence text in the case it is broken and it does not contain last line.
  my @tmpLicence;
  my $headerStage = 0;
  my $firstLineOfLicence ='';
  foreach my $line (@data){
    if($line =~ m($oldLicence[$licenceLineNumber])i ){
      push @tmpLicence, $line; 
      $headerStage = 3;  # We are inside the licence text
      $licenceLineNumber++;
      if($licenceLineNumber == $#oldLicence){  # We reached the end of the licence text
        @tmpLicence = ();
        push @result, @newLicence;
        print "   Licence text changed \n" if($options{v});
        $headerStage = 4; 
      }
    } 
    elsif($headerStage == 3){  # We are inside the licence text but actual line is not correct
      push @result, @tmpLicence;
      @tmpLicence = ();
      push @result, $line;
      $headerStage == 4;
    }
    else{ # ordinary line 
      if(($headerStage == 0) && ((!($line =~ m[^\s*//])) && (!($line =~ m[^\s*#]))&& (!($line =~ m[^\s*$])))){  #we are at the beginning of the file and we reachech line which is not a comment nor preprocesor directive and not empty
        if($options{'p'}){ 
          push @result, @newLicence;
          print "   Licence text added \n" if($options{v});
        }
        $headerStage = 4;
      }
      push @result, $line;
    }
  }
  push @result, @tmpLicence ;
  return @result;
}

sub changeDoubleInclusionLock{
  my @result;
  my $fileName = shift @_;

  if($fileName =~ /\/include\/capd\/([^\/]+)\/([^\/]+)\.(h\w*)$/){ # header files that are in separated modules/directories
    $stringToDefine = '_CAPD_'.uc($1).'_'.uc($2).'_'.uc($3).'_';
  }
  elsif($fileName =~ /\/include\/capd\/([^\/]+)\.(h\w*)$/){        # headers for facades 
    $stringToDefine = '_CAPD_'.uc($1).'_'.uc($2).'_';
  }
  elsif($fileName =~ /\/include\/([^\/]+)\/([^\/]+)\.(h\w*)$/){    # header files in for previous versions of capd (not in capd directory)
    $stringToDefine = '_CAPD_'.uc($1).'_'.uc($2).'_'.uc($3).'_';
  } 
  elsif ($fileName =~ /\/([^\/]+)\/([^\/]+)\/([^\/]+)\.(h\w*)$/){  # header files not in include directory (i.e. examples, programs, tests)
    $stringToDefine = '_CAPD_'.uc($1).'_'.uc($2).'_'.uc($3).'_'.uc($4).'_';
  } 
  else{
    return @_;
  }
  my $level = 0;
  my $isChanged = 0;  
  my $oldName ='';
  my $lookForDefine = 0;
  my $lineBuffor ='';
  my $lockLevel = -100;  
  foreach my $line (@_){
#    if((!($line =~ m[^\s*//])) && (!($line =~ m[^\s*#]))&& (!($line =~ m[^\s*$]))){
#      $isChanged = 1;
#    }
    if($lookForDefine){
      if($line =~ /^\s*$/){
        $lineBuffor .= $line;
        next;
      }
      $lookForDefine = 0;    
# we check if #ifndef XXX has corresponding #define XXX
      if($line =~ /^[^\/]*#\s*define\s*$oldName/){
        push @result, "#ifndef $stringToDefine $enter#define $stringToDefine $enter";
        print "   change: #ifndef  $oldName => $stringToDefine \n"  if(($options{'v'}) && ($oldName ne $stringToDefine)); 
        $lockLevel = $level-1;
        $isChanged = 1;
      }else{
        push @result, $lineBuffor;
        $lineBuffor = '';
        redo;
      }
    }  
    elsif((!$isChanged) && (($line =~ /^[^\/]*#\s*ifndef\s*(\S*)/) || ($line =~ /^[^\/]*#\s*if\s*!\s*defined\s*\(\s(\S*)\s*\)/))) {
      $lookForDefine = 1;
      $oldName = $1;
      $lineBuffor = $line;
      $level++;
      
    }
    else{
      if($line =~ /^[^\/]*#\s*if(n?def)?/){
        $level++;
      }
      elsif($line =~ /^[^\/]*#\s*endif/){
        $level--;
        if($level == $lockLevel){
          print "   change: #endif \/\/ $stringToDefine \n" if(($options{'v'}) && ($oldName ne $stringToDefine));
          push @result, "#endif \/\/ $stringToDefine $enter";
          $lockLevel = -100;
          next;
        }
      }
      push @result, $line;    
    }
  }
  return @result;    
}

sub processFile {
  my $name = $_[0];
  my @result = loadFile($name);
  system('cp', $name, $name.'.bak') if($options{b});
  @result = changeDoubleInclusionLock($name, @result) if($options{d});
  @result = changeLicence(@result) if($options{l});
  @result = doxygenCorrectFileName($name, @result) if($options{'f'});
  open(OUT, '>', $name);
  print OUT @result;
  close(OUT);
}

sub processDir{
  my $dirName = $_[0];
  opendir(DIR, $dirName);
  my @files = readdir(DIR);
  close DIR;
  my @dirsNames;
  foreach my $file (@files){
    $fullFileName = $dirName.'/'.$file;
    if(($file =~ /\.c(pp)?$/) || ($file =~ /\.h(pp)?$/)){
      print " processing file: $file\n";
      processFile($fullFileName);
    }
    if((-d $fullFileName) && ($file ne '..') && ($file ne '.')){
       push @dirsNames, $fullFileName;
    }
  }
  foreach $dir (@dirsNames){
    print "entering directory $dir\n";
    processDir($dir);
  }
}

sub processOption{
  my $option = $_[0];
  my $sign = (substr( $option, 0,1) eq '-')? 0: 1;
  
  for( $i = 1; $i < length $option; $i++){
    my $letter = substr( $option, $i, 1);
    if($letter eq 'a'){
      processOption(($sign? '+':'-').$allOptionsList);
    }
    else{
      $options{$letter} = $sign;
    }
  }
}

if ($#ARGV >= 0){   
  processOption($defaultOptionsList);
  foreach my $parameter (@ARGV){
    if($parameter =~ /^[+-]/){
     processOption($parameter);
    }
    else{
      if($parameter =~ /(.+)\/$/){
        $parameter = $1;
      }
      if(-d $parameter){  
        processDir($parameter);
      }
      else{
        processFile($parameter);
      }
    }
  }
}
else{
  help();
}
print "\n";
