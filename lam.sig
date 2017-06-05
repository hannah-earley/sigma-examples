(inh "prelude" ~1 ~2 ~3 ~4)
(inh "nat" + +' succ zero
           cmp cmp' cmp'ge cmp'ge'
           lt eq gt ge )

(beq idx lam app subx)
(grp (beq ~1@idx ~2@lam ~3@app ~4@subx))

;; perform a recursive-descent substitution in a prepped term y (where
;; to-be-replaced variables have been marked as subx) for x, return
;; substitution history
(beq subst subst')
(grp
  (perm* (subst x {~y y} #)
         (~y [`subst'idx `subst'lam `subst'app `subst'sub] {x y} subst))
    (perm (subst'idx [`subst `subst'lam `subst'app `subst'sub] {x n} `idx)
          (`idx [`subst' `subst'lam'3 `subst'app' `subst'sub] {{`idx n} # x} subst'idx))
    (perm (subst'lam [`subst'idx `subst `subst'app `subst'sub] {x t} `lam)
          (`subst'lam'1 (`unshift x #) t subst'lam))
      (perm (subst'lam'1 (# x' `unshift') t `subst'lam)
            (`subst'lam'2 (`subst x' t #) subst'lam'1))
      (perm (subst'lam'2 (# t' h x' `subst') `subst'lam'1)
            (`subst'lam'3 (# x' `unshift') t' h subst'lam'2))
      (perm (subst'lam'3 (`unshift x #) t' h `subst'lam'2)
            (`lam [`subst'idx `subst' `subst'app' `subst'sub]
                  {{`lam t'} h x} subst'lam'3))
    (perm (subst'app [`subst'idx `subst'lam `subst `subst'sub] {x {s t}} `app)
          (`subst'app' (`subst x s #) (`subst x t #) subst'app))
      (perm (subst'app' (# s' hs x `subst') (# t' ht x `subst') `subst'app)
            (`app [`subst'idx `subst'lam'3 `subst' `subst'sub]
                  {{`app {s' t'}} {hs ht} x} subst'app'))
    (perm (subst'sub [`subst'idx `subst'lam `subst'app `subst] {x #} `subx)
          (`subx [`subst'idx `subst'lam'3 `subst'app' `subst'] {x # x} subst'sub))
  (perm* (subst' [`subst'idx `subst'lam'3 `subst'app' `subst'sub] {z h x} ~y)
         (# z {~y h} x subst')))

(beq shift shift')
(grp
  (perm* (shift m {~x x} #) (~x [`shift'idx `shift'lam `shift'app] {m x} shift))

    (perm (shift'idx [`shift `shift'lam `shift'app] {m n} `idx)
          (`shift'idx'sw (`cmp n m #) shift'idx))
      (perm (shift'idx'sw (# ~m?n m-n `cmp') `shift'idx)
            (~m?n [`shift'idx'lt `shift'idx'eq `shift'idx'gt]
                  m-n shift'idx'sw))
        (perm (shift'idx'lt [`shift'idx'sw `shift'idx'eq `shift'idx'gt] m-n `lt)
              (`lt [`shift'idx'join # `shift'idx'gt] m-n shift'idx'lt))
        (perm (shift'idx'eq [`shift'idx'lt `shift'idx'sw `shift'idx'gt] m `eq)
              (`subx [`shift'idx' `shift'lam' `shift'app' `shift'] {m #} shift'idx'eq))
        (perm (shift'idx'gt [`shift'idx'lt `shift'idx'eq `shift'idx'sw] {m {`succ n-1-m}} `gt)
              (`ge [`shift'idx'lt # `shift'idx'join] {m n-1-m} shift'idx'gt))
      (perm (shift'idx'join [`shift'idx'lt # `shift'idx'gt] m-n ~m?n)
            (`shift'idx' (# ~m?n m-n `cmp'ge') shift'idx'join))
    (perm (shift'idx' (`cmp'ge n-1 m #) `shift'idx'join)
          (`idx [`shift' `shift'lam' `shift'app' `shift'idx'eq] {m n-1} shift'idx'))

    (perm (shift'lam [`shift'idx `shift `shift'app] {m t} `lam)
          (`shift'lam' (`shift {`succ m} t #) shift'lam))
    (perm (shift'lam' (# {`succ m} t' `shift') `shift'lam)
          (`lam [`shift'idx' `shift' `shift'app' `shift'idx'eq] {m t'} shift'lam'))

    (perm (shift'app [`shift'idx `shift'lam `shift] {m {s t}} `app)
          (`shift'app' (`shift m s #) (`shift m t #) shift'app))
    (perm (shift'app' (# m s' `shift') (# m t' `shift') `shift'app)
          (`app [`shift'idx' `shift'lam' `shift' `shift'idx'eq] {m {s' t'}} shift'app'))

  (perm* (shift' [`shift'idx' `shift'lam' `shift'app' `shift'idx'eq] {m x} ~x)
         (# m {~x x} shift')))

(beq prep prep')
(grp
  (perm* (prep t #) (`prep' (`shift 1 t #) prep))
  (perm* (prep' (# 1 t' `shift') `prep) (# t' prep')))

(grp
  (perm* (unshift t #) (`unshift' (# 1 t `shift') unshift))
  (perm* (unshift' (`shift 1 t' #) `unshift) (# t' unshift')))
