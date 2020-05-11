# Revision history for random

## 2.0.0.0  -- YYYY-mm-dd

# 1.2

1. Breaking change which mostly maintains backwards compatibility.
2. Support for monadic generators e.g. [mwc-random](https://hackage.haskell.org/package/mwc-random).
3. Monadic adapters for pure generators (providing a uniform monadic
   interface to pure and monadic generators).
4. Faster by more x10 (depending on the type) - see below for benchmarks.
5. Passes a large number of random number test suites:
  * [dieharder](http://webhome.phy.duke.edu/~rgb/General/dieharder.php "venerable")
  * [TestU01 (SmallCrush, Crush, BigCrush)](http://simul.iro.umontreal.ca/testu01/tu01.html "venerable")
  * [PractRand](http://pracrand.sourceforge.net/ "active")
  * [gjrand](http://gjrand.sourceforge.net/ "active")
  * See [random-quality](https://github.com/tweag/random-quality)
		 for details on how to do this yourself.
6. Better quality split as judged by these
	[tests](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/evaluation-of-splittable-pseudorandom-generators/3EBAA9F14939C5BB5560E32D1A132637). Again
	see [random-quality](https://github.com/tweag/random-quality) for
	details on how to do this yourself.
7. Unbiased generation of ranges.
8. Updated tests and benchmarks.
9. [Continuous integration](https://travis-ci.org/github/idontgetoutmuch/random).
10. Fully documented - for more details see the [haddock](https://htmlpreview.github.io/?https://github.com/idontgetoutmuch/random/blob/release-notes/docs/System-Random.html).

## Benchmarks

### Notes

1. These are **not** percentage (%) increases. Random `Int`s are produced 48.9 times faster!
2. The only type for which generation is slower is for `Integer`s (on
   ranges); in the version 1.1 the generation for `Integer` was
   biased.

### Without Specifying Ranges

    |----------|----------------|----------------|----------------------|
	| Type     | Cycles/Int 1.1 | Cycles/Int 1.2 | Performance Increase |
	|----------|----------------|----------------|----------------------|
	| Ints     |           1508 |          30.84 |                 48.9 |
	| Word16   |            495 |          30.88 |                 16.0 |
	| Floats   |           1036 |          35.11 |                 29.5 |
	| CFloats  |           1054 |          33.75 |                 31.2 |
	| Doubles  |           1875 |          35.77 |                 52.4 |
	| CDoubles |            908 |          33.31 |                 27.3 |
	| Integers |           1578 |          33.09 |                 47.7 |
	| Bools    |            698 |          36.15 |                 19.3 |
	| Chars    |            693 |           57.6 |                 12.0 |
	|----------|----------------|----------------|----------------------|

### Specifying Ranges

	|--------------|----------------|----------------|----------------------|
	| Type         | Cycles/Int 1.1 | Cycles/Int 1.2 | Performance Increase |
	|--------------|----------------|----------------|----------------------|
	| Ints         |            734 |            102 |                  7.2 |
	| Word16s      |            748 |            115 |                  6.5 |
	| Floats       |           2055 |          35.88 |                 57.3 |
	| CFloats      |           1071 |          34.96 |                 30.6 |
	| Doubles      |           3050 |          35.89 |                 85.0 |
	| CDoubles     |           1112 |          34.87 |                 31.9 |
	| Integers     |            534 |            868 |                  0.6 |
	| Bools        |            739 |          35.22 |                 21.0 |
	| Chars        |            790 |            133 |                  5.9 |
	| BIG Integers |         199848 |         103056 |                  1.9 |
	|--------------|----------------|----------------|----------------------|




