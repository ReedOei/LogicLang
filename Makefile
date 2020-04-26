all:
	kompile --backend java logic.k
	krun --verbose test1.lgc --log-cells "(states)" --log

