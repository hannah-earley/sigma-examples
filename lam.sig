(inh "prelude" ~1 ~2 ~3 ~4)
(inh "nat" + +' succ zero
           cmp cmp' cmp'ge cmp'ge'
           lt eq gt ge )

(beq idx lam app)
(grp (beq ~1@idx ~2@lam ~3@app ~4@subx))

;; perform a recursive-descent substitution of index m for x,
;; remembering that indices increase inside lambdas; also returns
;; substitution history
(beq subst subst')
(grp
  (perm* (subst m x {~y y} #)
         (~y [`subst'idx `subst'lam `subst'app] {m x y} subst))

    ;; de Bruijn index
    (perm (subst'idx [`subst `subst'lam `subst'app] {m x n} `idx)
          (`subst'idx'sw (`cmp m n #) x subst'idx))

      (perm (subst'idx'sw (# ~m?n m-n `cmp') x `subst'idx)
            (~m?n [`subst'idx'lt `subst'idx'eq `subst'idx'gt]
                  {m-n x} subst'idx'sw))

        (perm (subst'idx'lt [`subst'idx'sw `subst'idx'eq `subst'idx'gt]
                            {m-n x} ~m?n)
              (~m?n [`subst'idx'ne # `subst'idx'gt] {m-n x} subst'idx'lt))

        (perm (subst'idx'eq [`subst'idx'lt `subst'idx'sw `subst'idx'gt]
                            {n x} `eq)
              (`~2 [`subst'idx'ne' `subst'idx'] {x n x} subst'idx'eq))
        (perm (subst'idx'gt [`subst'idx'lt `subst'idx'eq `subst'idx'sw]
                            {m-n x} ~m?n)
              (~m?n [`subst'idx'lt # `subst'idx'ne] {m-n x} subst'idx'gt))

      (perm (subst'idx'ne [`subst'idx'lt # `subst'idx'gt] {m-n x} ~m?n)
            (`subst'idx'ne' (# ~m?n m-n `cmp') x subst'idx'ne))
      (perm (subst'idx'ne' (`cmp m n #) x `subst'idx'ne)
            (`~1 [`subst'idx' `subst'idx'eq] {{`idx n} m x} subst'idx'ne'))

    (perm (subst'idx' [`subst'idx'ne' `subst'idx'eq] {z m x} h)
          (`idx [`subst' `subst'lam' `subst'app'] {z h m x} subst'idx'))

    ;; lambda
    (perm (subst'lam [`subst'idx `subst `subst'app] {m x y'} `lam)
          (`subst'lam' (`subst {`succ m} x y' #) subst'lam))
    (perm (subst'lam' (# z h {`succ m} x `subst') `subst'lam)
          (`lam [`subst'idx' `subst' `subst'app']
                {{`lam z} h m x} subst'lam'))

    ;; application
    (perm (subst'app [`subst'idx `subst'lam `subst] {m x {y1 y2}} `app)
          (`subst'app' (`subst m x y1 #) (`subst m x y2 #) subst'app))
    (perm (subst'app' (# z1 h1 m x `subst') (# z2 h2 m x `subst') `subst'app)
          (`app [`subst'idx' `subst'lam' `subst']
                 {{`app {z1 z2}} {h1 h2} m x} subst'app'))

  (perm (subst' [`subst'idx' `subst'lam' `subst'app'] {z h m x} ~h)
        (# z {~h h} m x subst')))

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

(beq unshift unshift')
(grp
  (perm* (unshift t #) (`unshift' (# 1 t `shift') unshift))
  (perm* (unshift' (`shift 1 t' #) `unshift) (# t' unshift')))
