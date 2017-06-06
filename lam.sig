(inh "prelude" ~1 ~2 ~3 ~4 ~5 ~6 true false)
(inh "nat" + +' succ zero
           cmp cmp' cmp'ge cmp'ge'
           lt eq gt ge )

(beq var lam app)
(grp (beq ~1@var ~2@lam ~3@app ~4@subx))

; iterative normal-order evaluator
(beq eval eval')
(grp
  (perm* (eval t #) (`zero [`eval'loop `eval't] {t # #} eval))

  (perm (eval'loop [`eval `eval't] {t h n'} ~n)
        (`eval'red (`reduce t #) {h {~n n'}} eval'loop))
  (perm (eval'red (# t' h' c? `reduce') {h n} `eval'loop)
        (c? [`eval'f `eval't] {t' h' h n} eval'red))

    (perm (eval'f [`eval'red `eval't] {t' h' h n} `false)
          (`eval' (# t' h' `false `reduce') {h n} eval'f))

    (perm (eval't [`eval'f `eval'red] {t' h' h n} `true)
          (`succ [`eval `eval'loop] {t' {h' h} n} eval't))

  (perm* (eval' (`reduce t #) {h n} `eval'f) (# n t h eval')))

; normal-order reduction
(beq reduce reduce')
(grp
  (perm* (reduce {~t t} #) (~t [`red'var `red'lam `red'app] t reduce))

    (grp (beq
      red'var@r1
      red'lam'@r2
      redap'var'@r3
      redap'lam'@r4
      redap'app'2t@r5
      redap'app'3@r6))

    (perm (red'var [`reduce `red'lam `red'app] n `var)
          (`~1 [`reduce' `r2 `r3 `r4 `r5 `r6] {{`var n} # `false} red'var))

    (perm (red'lam [`red'var `reduce `red'app] s `lam)
          (`red'lam' (`reduce s #) red'lam))
      (perm (red'lam' (# s' h c? `reduce') `red'lam)
            (`~2 [`r1 `reduce' `r3 `r4 `r5 `r6] {{`lam s'} h c?} red'lam'))

    (perm (red'app [`red'var `red'lam `reduce] {{~r r} s} `app)
      (~r [`redap'var `redap'lam `redap'app] {r s} red'app))

      (perm (redap'var [`red'app `redap'lam `redap'app] {n s} `var)
            (`redap'var' {`var n} (`reduce s #) redap'var))
      (perm (redap'var' r (# s' hs c? `reduce') `redap'var)
            (`~3 [`r1 `r2 `reduce' `r4 `r5 `r6] {{`app {r s'}} hs c?} redap'var'))

      (perm (redap'lam [`redap'var `red'app `redap'app] {r s} `lam)
            (`redap'lam'1 (`prep r #) s redap'lam))
      (perm (redap'lam'1 (# r' `prep') s `redap'lam)
            (`redap'lam' (`subst s r' #) redap'lam'1))
      (perm (redap'lam' (# t h s `subst') `redap'lam'1)
            (`~4 [`r1 `r2 `r3 `reduce' `r5 `r6] {t {s h} `true} redap'lam'))

      (perm (redap'app [`redap'var `redap'lam `red'app] {r s} `app)
            (`redap'app'1 (`reduce {`app r} #) s redap'app))
      (perm (redap'app'1 (# r' hr c? `reduce') s `redap'app)
            (c? [`redap'app'2f `redap'app'2t] {r' s hr} redap'app'1))
        (perm (redap'app'2f [`redap'app'1 `redap'app'2t] {r s hr} `false)
              (`redap'app'3 (# r hr `false `reduce') (`reduce s #) redap'app'2f))
          (perm (redap'app'3 (`reduce r #) (# s hs c? `reduce') `redap'app'2f)
                (`~6 [`r1 `r2 `r3 `r4 `r5 `reduce'] {{`app {r s}} hs c?} redap'app'3))
        (perm (redap'app'2t [`redap'app'2f `redap'app'1] {r' s hr} `true)
              (`~5 [`r1 `r2 `r3 `r4 `reduce' `r6] {{`app {r' s}} hr `true} redap'app'2t))

  (perm* (reduce' [`r1 `r2 `r3 `r4 `r5 `r6] {t' h c?} ~r) (# t' {~r h} c? reduce')))

;; perform a recursive-descent substitution in a prepped term y (where
;; to-be-replaced variables have been marked as subx) for x, return
;; substitution history
(grp
  (perm* (subst x {~y y} #)
         (~y [`subst'var `subst'lam `subst'app `subst'sub] {x y} subst))
    (perm (subst'var [`subst `subst'lam `subst'app `subst'sub] {x n} `var)
          (`var [`subst' `subst'lam'3 `subst'app' `subst'sub] {{`var n} # x} subst'var))
    (perm (subst'lam [`subst'var `subst `subst'app `subst'sub] {x t} `lam)
          (`subst'lam'1 (`unshift x #) t subst'lam))
      (perm (subst'lam'1 (# x' `unshift') t `subst'lam)
            (`subst'lam'2 (`subst x' t #) subst'lam'1))
      (perm (subst'lam'2 (# t' h x' `subst') `subst'lam'1)
            (`subst'lam'3 (# x' `unshift') t' h subst'lam'2))
      (perm (subst'lam'3 (`unshift x #) t' h `subst'lam'2)
            (`lam [`subst'var `subst' `subst'app' `subst'sub]
                  {{`lam t'} h x} subst'lam'3))
    (perm (subst'app [`subst'var `subst'lam `subst `subst'sub] {x {s t}} `app)
          (`subst'app' (`subst x s #) (`subst x t #) subst'app))
      (perm (subst'app' (# s' hs x `subst') (# t' ht x `subst') `subst'app)
            (`app [`subst'var `subst'lam'3 `subst' `subst'sub]
                  {{`app {s' t'}} {hs ht} x} subst'app'))
    (perm (subst'sub [`subst'var `subst'lam `subst'app `subst] {x #} `subx)
          (`subx [`subst'var `subst'lam'3 `subst'app' `subst'] {x # x} subst'sub))
  (perm* (subst' [`subst'var `subst'lam'3 `subst'app' `subst'sub] {z h x} ~y)
         (# z {~y h} x subst')))

(grp
  (perm* (shift m {~x x} #) (~x [`shift'var `shift'lam `shift'app] {m x} shift))

    (perm (shift'var [`shift `shift'lam `shift'app] {m n} `var)
          (`shift'var'sw (`cmp n m #) shift'var))
      (perm (shift'var'sw (# ~m?n m-n `cmp') `shift'var)
            (~m?n [`shift'var'lt `shift'var'eq `shift'var'gt]
                  m-n shift'var'sw))
        (perm (shift'var'lt [`shift'var'sw `shift'var'eq `shift'var'gt] m-n `lt)
              (`lt [`shift'var'join # `shift'var'gt] m-n shift'var'lt))
        (perm (shift'var'eq [`shift'var'lt `shift'var'sw `shift'var'gt] m `eq)
              (`subx [`shift'var' `shift'lam' `shift'app' `shift'] {m #} shift'var'eq))
        (perm (shift'var'gt [`shift'var'lt `shift'var'eq `shift'var'sw] {m {`succ n-1-m}} `gt)
              (`ge [`shift'var'lt # `shift'var'join] {m n-1-m} shift'var'gt))
      (perm (shift'var'join [`shift'var'lt # `shift'var'gt] m-n ~m?n)
            (`shift'var' (# ~m?n m-n `cmp'ge') shift'var'join))
    (perm (shift'var' (`cmp'ge n-1 m #) `shift'var'join)
          (`var [`shift' `shift'lam' `shift'app' `shift'var'eq] {m n-1} shift'var'))

    (perm (shift'lam [`shift'var `shift `shift'app] {m t} `lam)
          (`shift'lam' (`shift {`succ m} t #) shift'lam))
    (perm (shift'lam' (# {`succ m} t' `shift') `shift'lam)
          (`lam [`shift'var' `shift' `shift'app' `shift'var'eq] {m t'} shift'lam'))

    (perm (shift'app [`shift'var `shift'lam `shift] {m {s t}} `app)
          (`shift'app' (`shift m s #) (`shift m t #) shift'app))
    (perm (shift'app' (# m s' `shift') (# m t' `shift') `shift'app)
          (`app [`shift'var' `shift'lam' `shift' `shift'var'eq] {m {s' t'}} shift'app'))

  (perm* (shift' [`shift'var' `shift'lam' `shift'app' `shift'var'eq] {m x} ~x)
         (# m {~x x} shift')))

(grp
  (perm* (prep t #) (`prep' (`shift 1 t #) prep))
  (perm* (prep' (# 1 t' `shift') `prep) (# t' prep')))

(grp
  (perm* (unshift t #) (`unshift' (# 1 t `shift') unshift))
  (perm* (unshift' (`shift 1 t' #) `unshift) (# t' unshift')))
