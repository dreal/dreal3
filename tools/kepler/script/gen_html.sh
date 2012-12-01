#!/bin/bash
TEMP=`mktemp`
TARGET=/afs/cs.cmu.edu/usr/soonhok/www/kepler/index.html
mkdir -p ~/www/kepler
cat header.html > $TEMP
./gen_stat.sh >> $TEMP
./gen_table.py >> $TEMP
cat footer.html >> $TEMP
mv $TEMP $TARGET
mkdir -p ~/www/kepler/flyspeck_ineqs
cp -avu flyspeck_ineqs/* ~/www/kepler/flyspeck_ineqs/
mkdir -p ~/www/kepler/result
cp -avu result/* ~/www/kepler/result/
cp -avu css/* ~/www/kepler/
cp -avu js/* ~/www/kepler/
