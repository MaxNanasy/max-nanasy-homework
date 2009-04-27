#!/bin/sh

cd ..
echo "---------- COMPILING ----------"
javac -g *.java || exit 1
SUFF=tst
for test in tests/*.$SUFF
do
	echo "-------- Running test $test --------"
	echo "java Scanner $test"
	java Scanner $test
	echo "diff -b $test.out ${test%.$SUFF}.out"
	diff -b $test.out ${test%.$SUFF}.out
done

exit 0
