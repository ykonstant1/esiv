/-!
  © 2024 Ioannis Konstantoulas. All rights reserved.

  This is a Lean implementation of the Sieve of Eratosthenes with wheel factorization using the
  primes 2, 3, and 5.  The 8 coprime classes modulo 2*3*5=30 are bitpacked into a ByteArray whose
  entry k and offset i represent the number 30*k + r(i), r(i) being the i-th coprime class in
  increasing order.  The array is traversed sequentially sifting out multiples of primes already
  determined by previous sifting.  No segmentation, parallelism or other optimizations are done.

  The core public function is primeSieveWheel (m : Nat) (exact : Bool := false) which returns
  the primes up to m if exact is true, otherwise returns the primes up to the nearest multiple of 30
  that is at least m.
 
  #eval Lean.versionString -- "4.7.0-rc2"
-/

/-- Convenient shorthand for making ByteArrays -/
@[inline] private
abbrev Array.toByteArray := ByteArray.mk

/-- Unpack bitpacked logic -/
@[inline] private
abbrev UInt8.toBool (b : UInt8) :=
  ((b >>> 0) &&& 1 == 1,
   (b >>> 1) &&& 1 == 1,
   (b >>> 2) &&& 1 == 1,
   (b >>> 3) &&& 1 == 1,
   (b >>> 4) &&& 1 == 1,
   (b >>> 5) &&& 1 == 1,
   (b >>> 6) &&& 1 == 1,
   (b >>> 7) &&& 1 == 1,)

/-- Repeat byte array s n times -/
@[inline] private
def ByteArray.repeat (n : Nat) (s : ByteArray) :=
  let M := ByteArray.mkEmpty <| n * s.size
  let S := ByteArray.mkEmpty <| n * s.size
  let M := ByteArray.copySlice s 0 M 0 s.size
  let S := ByteArray.copySlice s 0 S 0 s.size
  let rec loop (t : Nat) (sofar : ByteArray) (app : ByteArray) :=
    if t > 0 then
      loop (t / 2) (cond (t % 2 == 0) sofar (sofar ++ app)) (app ++ app)
    else
      sofar
  if n == 0 then M else loop (n - 1) S M

/-- Return increment for the next element of (ℤ/30ℤ)× --/
@[inline] private
abbrev Nat.inc (j : Nat) :=
  match j % 30 with
  |  1 => 6
  |  7 => 4
  | 11 => 2
  | 13 => 4
  | 17 => 2
  | 19 => 4
  | 23 => 6
  | 29 => 2
  | _  => 1

/-- Return mask for the offset corresponding to each class mod 30. -/
@[inline] private
abbrev UInt8.toMask : UInt8 → UInt8
  |  1 => 254
  |  7 => 253
  | 11 => 251
  | 13 => 247
  | 17 => 239
  | 19 => 223
  | 23 => 191
  | 29 => 127
  | _  => 0

/-- Update the entries of B by (b := B[k]) ↦ f(r,b) where k is the array entry
    given by (i*j)/30 and r is the mod 30 class of (i*j) representing the bit-offset
    in the entry. -/
@[inline, specialize] private partial
def ByteArray.updateProgression (B : ByteArray) (i j N : Nat)
    (f : UInt8 → UInt8 → UInt8) : ByteArray :=
  let p := i * j
  if p > N then B else
    let k := p / 30
    let r := p % 30 |>.toUInt8
    let J := j + j.inc
    B.set! k (f r <| B.get! k)
    |>.updateProgression i J N f

/-- Use updateProgression to sift out multiples of i in B
    starting from the multiple i². -/
@[inline] private
abbrev ByteArray.siftOut (B : ByteArray) (i n : Nat) :=
  B.updateProgression i i n
    fun x i ↦ x.toMask &&& i

/-! Main sifting function: traverse B looking for already determined primes
    corresponding to true values of the bit vector; for each prime, sift out
    all its multiples to the stopping point n. -/
@[inline] private partial
def ByteArray.sift (B : ByteArray) (k s n : Nat) :=
  if s < k then B else
    let (b0, b1, b2, b3, b4, b5, b6, b7) := B.get! k |>.toBool
    let B := cond b0 (B.siftOut (30*k +  1) n) B
    let B := cond b1 (B.siftOut (30*k +  7) n) B
    let B := cond b2 (B.siftOut (30*k + 11) n) B
    let B := cond b3 (B.siftOut (30*k + 13) n) B
    let B := cond b4 (B.siftOut (30*k + 17) n) B
    let B := cond b5 (B.siftOut (30*k + 19) n) B
    let B := cond b6 (B.siftOut (30*k + 23) n) B
    let B := cond b7 (B.siftOut (30*k + 29) n) B
    B.sift (k + 1) s n

/-- Return an upper bound for the number of primes up to n;
    convenient for minimizing memory allocation.  This bound
    is due to Pierre Dusart. -/
@[inline] private
def primeBound (n : Nat) :=
  let f := n.toFloat
  let g := f.log
  (f / g) * (1 + 1.2762 / g) |>.ceil.toUSize.toNat

@[inline] private
abbrev smallPrimes :=
  #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

/-! Return all primes up to m if m is a multiple of 30, otherwise up
    to the next multiple of 30 unless `exact` is true.  If m is up to 60,
    return all small primes. -/
def primeSieveWheel (m : Nat) (exact : Bool := false) :=
  let n   := if m % 30 == 0 then m else m + 30 - (m % 30)
  let out := if n ≤ 60 then smallPrimes else
    let k   := n / 30
    let bag := Array.mkEmpty (primeBound n)
               |>.push 2 |>.push 3 |>.push 5
    #[254].toByteArray ++
    #[255].toByteArray.repeat (k - 1)
    |>.sift 0 k n
    |>.foldl
      (fun (G, k) u ↦
        let (b0, b1, b2, b3, b4, b5, b6, b7) := u.toBool
        let G := cond b0 (G.push (30*k +  1)) G
        let G := cond b1 (G.push (30*k +  7)) G
        let G := cond b2 (G.push (30*k + 11)) G
        let G := cond b3 (G.push (30*k + 13)) G
        let G := cond b4 (G.push (30*k + 17)) G
        let G := cond b5 (G.push (30*k + 19)) G
        let G := cond b6 (G.push (30*k + 23)) G
        let G := cond b7 (G.push (30*k + 29)) G
        (G, k + 1))
      (bag, 0)
    |>.fst
  if exact then out.popWhile (. > m) else out

/-- Print out the number of primes found by the sieve;
    example main to test correctness and performance. --/
def main (args : List String) : IO Unit :=
  if let some n := args[0]? >>= String.toNat? then
    IO.println s!"{ primeSieveWheel n |>.size }"
  else
    IO.println "Invalid input: give a positive integer."
