#!/usr/bin/env bash


tail -n +11 matching.dict| while IFS=: read -r lhs rhs
do
	fn=$(git grep -l "$lhs")
	if [ -z "$fn" ];
	then echo "Failed $lhs:$rhs"
	fi
	# echo "Match $lhs::::$fn"
	sed -i "/$lhs/a $rhs" $fn
done
