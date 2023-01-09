rm *.out

for ex in react_examples/*
do
	for out in {our,original}.out
	do
		echo $(basename $ex) >> $out
		echo '======================================================' >> $out

		${1:-python3} react_mc_${out/.out/}.py $ex | grep -v 'Counterexample' >> $out

		echo '' >> $out
	done
done

[[ $(diff -u our.out original.out) ]] && echo No || echo Ok
