#!/bin/bash

TEMPFILE=$(pwd)/count.tmp
echo 0 > $TEMPFILE

rand=$((1 + $RANDOM % 32 ))

FILES=$(pwd)/benchmarks/*.c
for f in $FILES
do
  counter=$[$(cat $TEMPFILE) + 1]
  echo $counter > $TEMPFILE
  if [[ $counter -ne $rand ]]; then
    continue
  fi

  fullname=$(basename -- "$f")
  filename="${fullname%.*}"
  echo $filename

  ./selfie -c $f -o $filename
  ./ase -l $filename -timeout 18000 -pvi_ubox_bvt 1
  ./ase -l $filename -timeout 18000 -pvi_ubox_bvt 2
  ./ase -l $filename -timeout 18000 -pvi_bvt
  ./ase -l $filename -timeout 18000 -bvt
  rm $filename

  echo "-------------------------------------------------"
done

unlink $TEMPFILE