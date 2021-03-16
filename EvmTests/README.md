Based on test suite from
https://github.com/ethereum/tests/blob/develop/src/VMTestsFiller

Copy from here into Tests.

Then run e.g.

"ruby ./translate_all_tests.rb ./Tests/vmArithmeticTest"

to translate all the arithmetic tests.

or, to translate a single test, run e.g.

"ruby ./translate_test.rb ./Tests/vmArithmeticTest/add0Filler.json"
