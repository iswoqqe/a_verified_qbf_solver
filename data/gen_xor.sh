#!/bin/bash

if [[ $1 != +([0-9]) ]]
then
	echo "usage: $0 SIZE [MAKE_UNSAT]"
	exit 1
fi

if [[ $2 ]]
then
	echo p cnf $((2 * $1)) $((4 * $1 - 2 + 1))
else
	echo p cnf $((2 * $1)) $((4 * $1 - 2))
fi

for ((i = 0; i < $1; ++i))
do
	echo a $((2 * $i + 1)) 0
	echo e $((2 * $i + 2)) 0
done

if (($1 > 0))
then
	echo 1 2 0
	echo -1 -2 0
fi

for ((i = 1; i < $1; ++i))
do
	echo  $((2 * $i))  $((2 * $i + 1))  $((2 * $i + 2)) 0
	echo  $((2 * $i)) -$((2 * $i + 1)) -$((2 * $i + 2)) 0
	echo -$((2 * $i))  $((2 * $i + 1)) -$((2 * $i + 2)) 0
	echo -$((2 * $i)) -$((2 * $i + 1))  $((2 * $i + 2)) 0
done

if [[ $2 ]]
then
	for ((i = 0; i < $1; ++i))
	do
		echo -n "$((2 * $i + 2)) "
	done
	echo 0
fi
