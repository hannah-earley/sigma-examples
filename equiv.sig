(beq*)

(grp ; example of cyclic sequence
  (def* cyclic (t t f))
  (* ...
     (t t f)
     (t f t)
     (f t t)
     (t t f)
     ... *)

  (perm (t p q) (p q t))
  (perm (f p q) (q p f)))

(grp ; example of finite sequence
  (def* finite (foo #))

  (perm (foo #) (`bar 2 foo))
  (perm (bar n f) (# {f n} bar)))

(grp ; example of left-bounded sequence
  (def* left (qux #))
  (* (qux #)
     (zero [qux+ qux+] # qux)
     (qux+ [qux qux+] # zero)
     (succ [qux qux+] 0 qux+)
     (qux+ [qux qux+] 0 qux+)
     (succ [qux qux+] 1 qux+)
     ...
     (succ [qux qux+] 7890524 qux+)
     ... *)

  (inh "prelude" zero succ)
  (perm (qux #) (`zero [`qux+ `qux+] # qux))
  (perm (qux+ [`qux `qux+] n' ~n) (`succ [`qux `qux+] {~n n'} qux+)))

(grp ; example of right-bounded sequence
  (def* right (# quux))
  (* ...
     (quux- [quux quux-] 987254 succ)
     ...
     (quux- [quux quux-] 1 succ)
     (succ [quux quux-] 0 quux-)
     (quux- [quux quux-] 0 succ)
     (zero [quux quux-] # quux-)
     (quux [quux- quux-] # zero)
     (# quux) *)

  (inh "prelude" zero succ)
  (perm (quux- [`quux `quux-] {~n n'} `succ) (~n [`quux `quux-] n' quux-))
  (perm (quux [`quux- `quux-] # `zero) (# quux)))

(grp ; example of unbounded sequence
  (def* unbounded (baz [baz-n baz-0 baz+] 0 z))
    ; ^^ atom language bug, labels in [] marked yellow
  (* ...
     (baz [..] 6748230 -)
     ...
     (baz [..] 2 -)
     (- [..] 2 baz)
     (baz- [..] 2 -)
     (succ [..] 0 baz-)
     (baz-n [..] 0 succ)
     (- [..] 1 baz-n)
     (baz [..] 1 -)
     (- [..] 1 baz)
     (baz- [..] 1 -)
     (zero [..] # baz-)
     (baz-0 [..] # zero)
     (z [..] 0 baz-0)

  :: (baz [..] 0 z)

     (z [..] 0 baz)
     (baz+0 [..] 0 z)
     (zero [..] # baz+0)
     (baz+ [..] # zero)
     (+ [..] {succ {zero #}} baz+)
        = (+ [..] 1 baz+)
     (baz [..] 1 +)
     (+ [..] 1 baz)
     (baz+n [..] 1 +)
     (succ [..] 0 baz+n)
     (baz+ [..] 0 succ)
     (+ [..] 2 baz+)
     (baz [..] 2 +)
     ...
     (baz [..] 4259013 +)
     ... *)

  (inh "prelude" zero succ -@~1 z@~2 +@~3)

  (perm (baz [`baz-n `baz-0 `baz+] n ~sgn)
        (~sgn [`baz- `baz+0 `baz+n] n baz))

    (perm (baz- [`baz `baz+0 `baz+n] {`succ {~n n}} `-)
          (~n [`baz-0 `baz-n] n baz-))

      (perm (baz-0 [`baz- `baz-n] # `zero)
            (`z [`baz-n `baz `baz+] 0 baz-0))

      (perm (baz-n [`baz-0 `baz-] n'' `succ)
            (`- [`baz `baz-0 `baz+] {`succ n''} baz-n))

    (perm (baz+0 [`baz- `baz `baz+n] 0 `z)
          (`zero [`baz+ `baz+n] # baz+0))

    (perm (baz+n [`baz- `baz+0 `baz] {`succ n'} `+)
          (`succ [`baz+0 `baz+] n' baz+n))

      (perm (baz+ [`baz+0 `baz+n] n'' ~n)
            (`+ [`baz-n `baz-0 `baz] {`succ {~n n''}} baz+)))
