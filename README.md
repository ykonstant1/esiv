This is a Lean implementation of the Sieve of Eratosthenes with wheel factorization.
No segmentation, parallelism or other optimizations are done.

The main motivation was to test the performance of relatively unoptimized Lean code in some
arithmetic contexts where large arrays are necessary.  For small inputs approximately up to 2^{35},
the function performs approximately 200 times slower than the optimized
[primesieve](https://github.com/kimwalisch/primesieve).  Segmentation is required to push this
program to bigger inputs; I have left this to a future version of the code.
