(inh "prelude" zero succ)
(inh "prelude" ~1 ~2 ~3)
(beq zero succ)

;; should probably rewrite these in the form
;; <f z f' a # : # r f z f'>


; addition, (+ +' a b #) -> (# c b + +') where c == a+b
; we must retain some information about the original arguments
; so the most sensible thing is to just retain one ...
(beq + +')
(grp
  (perm* (+ a b #)
         (`zero [`loop `next] {a b #} +))

  (perm (loop [`+ `next] {a {~b b'} c'} ~c)
        (~b [`+' `next] {a b' {~c c'}} loop))

  (perm (next [`+' `loop] {a b c} `succ)
        (`succ [`+ `loop] {{`succ a} b c} next))

  (perm* (+' [`loop `next] {a # c} `zero)
         (# a c +')))

; ... by retaining one of the arguments in + we can immediately
; repurpose it for subtraction without writing a new function!
; below, we have wrapped the reverse of ++' in a forward interface --'
(beq - -')
(grp
  (perm* (- a b #) (`-' (# a b `+') -))
  (perm* (-' (`+ a b #) `-) (# a b -')))

; data Ord = LT | EQ | GT
; data Ord' = LE | NE | GE
(beq lt eq gt (**) le ne ge)
(grp (beq ~1@lt ~2@eq ~3@gt)
     (beq ~1@le ~2@ne ~3@ge))
(* the reason for this motif is:
    - we can't alias using (def lt ~1) for fear of infinite loops
    - a top-level (beq ~1@lt) doesn't expose lt to use within this file,
        so we must group it to add some indirection
    - we must then re-bequeath it to the outside world
    - might suggest using a grp* to auto-beq the contents of a group?
        seems that
    *)

; example of swapping lt(~1) and eq(~2) for ~2 and ~1 respectively
(beq test test')
(grp
  (perm* (test ord #)
         (ord [`test'l `test'e `test'g] # test))
  (perm (test'l [`test `test'e `test'g] # `lt)
        (`~2 [`test'e `test' `test'g] # test'l))
  (perm (test'e [`test'l `test `test'g] # `eq)
        (`~1 [`test' `test'l `test'g] # test'e))
  (perm (test'g [`test'l `test'e `test] # `gt)
        (`~3 [`test'e `test'l `test'] # test'g))
  (perm* (test' [`test'e `test'l `test'g] # ~n)
         (# ~n test')))

;; (cmp a b #) compares two numbers and returns either:
;;; (lt {a (b-a)})
;;; (eq a)
;;; (gt {b (a-b)})
(beq cmp cmp')
(grp
  (perm* (cmp a b #) (`zero [`cmp'l `cmp'bg] {a b #} cmp))
  (perm (cmp'l [`cmp `cmp'bg] {{~a a} b c'} ~c)
        (~a [`cmp'a0 `cmp'ag] {a b {~c c'}} cmp'l))
    (perm (cmp'a0 [`cmp'l `cmp'ag] {# {~b b-a} a} `zero)
          (~b [`cmp'ab0 `cmp'abg] {{~b b-a} a} cmp'a0))
      (perm (cmp'ab0 [`cmp'a0 `cmp'abg] {0 a} `zero)
            (`eq [`cmp'abg `cmp' `cmp'b0] a cmp'ab0))
      (perm (cmp'abg [`cmp'ab0 `cmp'a0] {b-a a} `succ)
            (`lt [`cmp' `cmp'ab0 `cmp'b0] {a b-a} cmp'abg))
    (perm (cmp'ag [`cmp'a0 `cmp'l] {a-r {~b b-r} r-1} `succ)
          (~b [`cmp'b0 `cmp'bg] {a-r b-r r-1} cmp'ag))
      (perm (cmp'b0 [`cmp'ag `cmp'bg] {a-b-1 # b} `zero) ;a > b because a /= 0
            (`gt [`cmp'abg `cmp'ab0 `cmp'] {b {`succ a-b-1}} cmp'b0))
      (perm (cmp'bg [`cmp'b0 `cmp'ag] {a-r b-r r-1} `succ)
            (`succ [`cmp `cmp'l] {a-r b-r r-1} cmp'bg))
  (perm* (cmp' [`cmp'abg `cmp'ab0 `cmp'b0] res ~ord)
         (# ~ord res cmp')))

(beq cmp'ge cmp'ge')
(grp
  (perm* (cmp'ge a b #) (`cmp'ge'sw (`cmp a b #) cmp'ge))
  (perm (cmp'ge'sw (# ~a?b a-b `cmp') `cmp'ge)
        (~a?b [`cmp'ge'lt `cmp'ge'eq `cmp'ge'gt] a-b cmp'ge'sw))
    (perm (cmp'ge'lt [`cmp'ge'sw `cmp'ge'eq `cmp'ge'gt] {a b-a} `lt)
          (`lt [`cmp'ge' # `cmp'ge'ge] {a b-a} cmp'ge'lt))
    (perm (cmp'ge'eq [`cmp'ge'lt `cmp'ge'sw `cmp'ge'gt] b `eq)
          (`zero [`cmp'ge'ge `cmp'ge'gt] {b #} cmp'ge'eq))
    (perm (cmp'ge'gt [`cmp'ge'lt `cmp'ge'eq `cmp'ge'sw] {b {`succ a-b'}} `gt)
          (`succ [`cmp'ge'eq `cmp'ge'ge] {b a-b'} cmp'ge'gt))
      (perm (cmp'ge'ge [`cmp'ge'eq `cmp'ge'gt] {b a-b'} ~a-b)
            (`ge [`cmp'ge'lt # `cmp'ge'] {b {~a-b a-b'}} cmp'ge'ge))
  (perm* (cmp'ge' [`cmp'ge'lt # `cmp'ge'ge] res ~ord)
         (# ~ord res cmp'ge')))

; (/% a b #) -> (# quotient remainer divisor /%')
(beq div@/% div'@/%')
(grp
  (perm* (div a b #) (`zero [`div'l `div'gt] {a b #} div))
  (perm (div'l [`div `div'gt] {r d q'} ~q)
        (`div'sw (`cmp r d #) {~q q'} div'l))
  (perm (div'sw (# ~r?d r-d `cmp') q `div'l)
        (~r?d [`div'lt `div'eq `div'gt] {r-d q} div'sw))
    (perm (div'lt [`div'sw `div'eq `div'gt] {{r d-r} q} `lt)
          (`div'lt' (`+ d-r r #) q div'lt))
    (perm (div'lt' (# d {`succ r'} `+') q `div'lt)
          (`succ [`div'eq `div'] {q r' d} div'lt'))
    (perm (div'eq [`div'lt `div'sw `div'gt] {d q'} `eq)
          (`zero [`div' `div'lt'] {{`succ q'} # d} div'eq))
    (perm (div'gt [`div'lt `div'eq `div'sw] {{d r} q} `gt)
          (`succ [`div `div'l] {r d q} div'gt))
  (perm* (div' [`div'eq `div'lt'] {q r' d} ~r) (# q {~r r'} d div')))

(beq mul-plus@*+ mul-plus'@*+' mul@* mul@*')
(grp
  (perm* (mul-plus a b c #) (`mul-plus' (# a c b `div') mul-plus))
  (perm* (mul-plus' (`div n b #) `mul-plus) (# n b mul-plus'))

  (perm* (mul a b #) (`mul' (`mul-plus a b 0 #) mul))
  (perm* (mul' (# n b `mul-plus') `mul) (# n b mul')))

;(perm* (triangle))

; cantor pairing function
(beq pair pair' unpair unpair')
(grp
  (perm* (pair x y #) (`pair' (# x y `unpair') pair))
  (perm* (pair' (`unpair n #) `pair) (# n pair'))

  (perm* (unpair n #) (`zero [`unpair'l `unpair'lt] {n #} unpair))
  (perm (unpair'l [`unpair `unpair'lt] {n x+y'} ~x+y)
        (`unpair'l' (`cmp {~x+y x+y'} n #) unpair'l))
  (perm (unpair'l' (# ~x?y xy `cmp') `unpair'l)
        (~x?y [`unpair'lt `unpair'eq `unpair'gt] xy unpair'l'))
    (perm (unpair'lt [`unpair'l' `unpair'eq `unpair'gt] {x+y n} `lt)
          (`succ [`unpair `unpair'l] {n x+y} unpair'lt))
    (perm (unpair'eq [`unpair'lt `unpair'l' `unpair'gt] x `eq)
          (`zero [`unpair' `unpair'gt] {x #} unpair'eq))
    (perm (unpair'gt [`unpair'lt `unpair'eq `unpair'l']
                     {{`succ y-1} {`succ x}} `gt)
          (`succ [`unpair'eq `unpair'] {x y-1} unpair'gt))
  (perm* (unpair' [`unpair'eq `unpair'gt] {x y'} ~y) (# x {~y y'} unpair')))

; triangle numbers
(beq triangle triangle')
(grp
  (perm* (triangle n #) (`triangle' (# n 0 `unpair') triangle))
  (perm* (triangle' (`unpair t #) `triangle) (# t triangle')))
