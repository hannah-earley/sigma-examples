(inh "prelude" ~1 ~2 ~3 ~4 ~5 true false)
(inh "nat" + +' succ zero
           cmp cmp' cmp'ge cmp'ge'
           lt eq gt ge )

(beq var lam app)
(grp (beq ~1@var ~2@lam ~3@app ~4@subx))

; the ~a flag is whether or not HNF has been reached (in the current branch),
; and thus whether we should reduce the RHSs of applications
(beq reduce reduce')
(grp
  (perm* (reduce {~t t} #) (~t [`reduce'var `reduce'lam `reduce'app] t reduce))

    (perm (reduce'var [`reduce `reduce'lam `reduce'app] n `var)
          (`~1 [`reduce' `reduce'lam' `redap'var'
                `redap'lam' `redap'app''] {{`var n} `false #} reduce'var))

    (perm (reduce'lam [`reduce'var `reduce `reduce'app] s `lam)
          (`reduce'lam' (`reduce s #) reduce'lam))
    (perm (reduce'lam' (# s' h `reduce') `reduce'lam)
          (`~2 [`reduce'var `reduce' `redap'var'
                `redap'lam' `redap'app''] {{`lam s'} `false h} reduce'lam'))

    (perm (reduce'app [`reduce'var `reduce'lam `reduce] {{~r r} s} `app)
          (~r [`redap'var' `redap'lam `redap'app] {r s} reduce'app))
      (perm (redap'var' [`reduce'app `redap'lam `redap'app] {n s} `var)
            (`~3 [`reduce'var `reduce'lam' `reduce'
                  `redap'lam' `redap'app'']
                 {{`app {{`var n} s}} `false #} redap'var'))
      ;(perm (redap'var [`reduce'app `redap'lam `redap'app] {n s} `var)
      ;      (`redap'var' (`redap'fin {`var n} s #) redap'var))
      ;(perm (redap'var' (# t h `redap'fin') `redap'var)
      ;      (`~3 [`reduce'var `reduce'lam' `reduce'
      ;            `redap'lam' `redap'app''] {t h} redap'var'))

      (perm (redap'lam [`redap'var' `reduce'app `redap'app] {q s} `lam)
            (`redap'lam' (`reduce'beta q s #) redap'lam))
        (perm (redap'lam' (# t h `reduce'beta') `redap'lam)
              (`~4 [`reduce'var `reduce'lam' `redap'var'
                    `reduce' `redap'app''] {t `true h} redap'lam'))

      (perm (redap'app [`redap'var' `redap'lam `reduce'app] {pq s} `app)
            (`redap'app' (`reduce {`app pq} #) s redap'app))
        (perm (redap'app' (# o {~a h} `reduce') s `redap'app)
              (`redap'app'' (`redap'fin ~a o s #) h redap'app'))
        (perm (redap'app'' (# t ~a h' `redap'fin') h `redap'app')
              (`~5 [`reduce'var `reduce'lam' `redap'var'
                    `redap'lam' `reduce'] {t ~a {h' h}} redap'app''))

  (perm* (reduce' [`reduce'var `reduce'lam' `redap'var'
                   `redap'lam' `redap'app''] {t' ~a h} ~h)
         (# t' {~a {~h h}} reduce')))

(grp
  (perm* (reduce'beta s t #) (`reduce'beta'1 (`prep s #) t reduce'beta))
  (perm (reduce'beta'1 (# s' `prep') t `reduce'beta)
        (`reduce'beta'2 (`subst t s' #) reduce'beta'1))
  (perm (reduce'beta'2 (# u h t `subst') `reduce'beta'1)
        (`reduce'beta' (`reduce u #) {t h} reduce'beta'2))
  (perm* (reduce'beta' (# v h' `reduce') h `reduce'beta'2)
         (# v {h h'} reduce'beta')))

(grp
  (perm* (redap'fin ~a s t #)
         (~a [`redap'fin'false `redap'fin'true] {s t} redap'fin))
    (perm (redap'fin'false [`redap'fin `redap'fin'true] {s t} `false)
          (`~1 [`redap'fin' `redap'fin'var `redap'fin'lam' `redap'fin'app']
               {{`app {s t}} `false #} redap'fin'false))
    (perm (redap'fin'true [`redap'fin'false `redap'fin] {{~s s} t} `true)
          (~s [`redap'fin'var `redap'fin'lam `redap'fin'app] {s t} redap'fin'true))
      (perm (redap'fin'var [`redap'fin'true `redap'fin'lam `redap'fin'app] {n t} `var)
            (`~2 [`redap'fin'false `redap'fin' `redap'fin'lam' `redap'fin'app']
                 {{`app {{`var n} t}} `true #} redap'fin'var))
      (perm (redap'fin'lam [`redap'fin'var `redap'fin'true `redap'fin'app] {s t} `lam)
            (`redap'fin'lam' (`reduce {`app {{`lam s} t}} #) redap'fin'lam))
        (perm (redap'fin'lam' (# u {~a h} `reduce') `redap'fin'lam)
              (`~3 [`redap'fin'false `redap'fin'var `redap'fin' `redap'fin'app']
                   {u ~a h} redap'fin'lam'))
      (perm (redap'fin'app [`redap'fin'var `redap'fin'lam `redap'fin'true] {s t} `app)
            (`redap'fin'app' {`app s} (`reduce t #) redap'fin'app))
        (perm (redap'fin'app' s (# t' h `reduce') `redap'fin'app)
              (`~4 [`redap'fin'false `redap'fin'var `redap'fin'lam' `redap'fin']
                   {{`app {s t'}} `true h} redap'fin'app'))
  (perm* (redap'fin' [`redap'fin'false `redap'fin'var
                      `redap'fin'lam' `redap'fin'app'] {u ~a h} ~h)
         (# u ~a {~h h} redap'fin')))

(grp(grp
  (perm* (redap'fin {~s s} t #)
          (~s ~BREAK~ [`redap'fin'var `redap'fin'lam `redap'fin'app]
              {s t} redap'fin))
    (perm (redap'fin'var [`redap'fin `redap'fin'lam `redap'fin'app] {n t} `var)
          (`redap'fin'var' n (`reduce t #) redap'fin'var))
      (perm (redap'fin'var' n (# t' h `reduce') `redap'fin'var)
            (`var [`redap'fin' `redap'fin'lam' `redap'fin'app']
                  {{`app {{`var n} t'}} h} redap'fin'var'))
    (perm (redap'fin'lam [`redap'fin'var `redap'fin `redap'fin'app] {s t} `lam)
          (`redap'fin'lam' (`reduce {`app {{`lam s} t}} #) redap'fin'lam))
      (perm (redap'fin'lam' (# u h `reduce') `redap'fin'lam)
            (`lam [`redap'fin'var' `redap'fin' `redap'fin'app']
                  {u h} redap'fin'lam'))
    (perm (redap'fin'app [`redap'fin'var `redap'fin'lam `redap'fin] {s t} `app)
          (`redap'fin'app' {`app s} (`reduce t #) redap'fin'app))
      (perm (redap'fin'app' s (# t' h `reduce') `redap'fin'app)
            (`app [`redap'fin'var' `redap'fin'lam' `redap'fin']
                  {{`app {s t'}} h} redap'fin'app'))
  (perm* (redap'fin' [`redap'fin'var' `redap'fin'lam' `redap'fin'app'] {u h} ~h)
         (# u {~h h} redap'fin'))))

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
