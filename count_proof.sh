#!/bin/sh
# usage : count_proof.sh file_name

sed -e 's/Proof.\ /Proof.\n/g' -e 's/ Qed./\nQed./g' $1 > tmp_$1
echo "Distribution"
awk '/Proof\./ { flag = 1; ctr=-2 } flag { ctr++ } /Qed./ { flag = 0; print ctr }' tmp_$1 | sort -n | uniq -c | sort -nr | sort -n -k 2
echo "Proof lines"
awk '/Qed\./ { flag = 0 } flag { print } /Proof./ { flag = 1 }' tmp_$1 | wc -l
rm tmp_$1
