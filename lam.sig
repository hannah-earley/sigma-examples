(inh "prelude" ~1 ~2 ~3 ~4)
(inh "nat" + +' succ zero
           cmp cmp' cmp'ge cmp'ge'
           lt eq gt ge )

(beq var lam app subx)
(grp (beq ~1@var ~2@lam ~3@app ~4@subx))

;; perform a recursive-descent substitution in a prepped term y (where
;; to-be-replaced variables have been marked as subx) for x, return
;; substitution history
(beq subst subst')
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

(beq shift shift')
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

(beq prep prep')
(grp
  (perm* (prep t #) (`prep' (`shift 1 t #) prep))
  (perm* (prep' (# 1 t' `shift') `prep) (# t' prep')))

(grp
  (perm* (unshift t #) (`unshift' (# 1 t `shift') unshift))
  (perm* (unshift' (`shift 1 t' #) `unshift) (# t' unshift')))
