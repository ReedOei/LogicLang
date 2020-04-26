all: test1 test2

test1: kompile test1.lgc
	krun --verbose test1.lgc # --log-cells "(states)" --log --log-func-eval

test2: kompile test2.lgc
	krun --verbose test2.lgc --log-cells "(states)" --log --log-func-eval

kompile: logic-kompiled/timestamp

logic-kompiled/timestamp: logic.k
	kompile --backend java logic.k

clean:
	rm -rf logic-kompiled/

