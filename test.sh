rm *.out

for ex in react_examples/*
do
	for out in {our,original}.out
	do
		echo $(basename $ex) >> $out
		echo '======================================================' >> $out

		${1:-python3} react_mc_${out/.out/}.py $ex >> $out

		echo '' >> $out
	done
done
