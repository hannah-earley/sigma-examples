(inh* "lam")

;; convenience function that exploits the interpreter not checking that perms
;; are indeed reversible to throw away history information for easier debugging
;(perm* (evil t #) (`evil' (`eval t #) evil))
;(perm* (evil' (# n t' h `eval') `evil) (# n t' evil'))

(inh "prelude" false true)
(inh "nat" zero succ)
(beq evil evil')
(grp
  (perm* (evil t #) (`zero [`evil'loop `evil't] {t #} evil))

  (perm (evil'loop [`evil `evil't] {t n'} ~n)
        (`evil'red (`reduce t #) {~n n'} evil'loop))
  (perm (evil'red (# t' h' c? `reduce') n `evil'loop)
        (c? [`evil' `evil't] {t' n} evil'red))

    (perm (evil't [`evil' `evil'red] {t' n} `true)
          (`succ [`evil `evil'loop] {t' n} evil't))

  (perm* (evil' [`evil'red `evil't] {t n} `false) (# n t evil')))

;; https://en.wikipedia.org/wiki/De_Bruijn_index
(def* wiki
  {app{
    {lam {lam {app{
      {app{ {var 4} {var 2} }}
      {lam {app{ {var 1} {var 3} }}} }}}}
    {lam {app{ {var 5} {var 1} }}} }})

(def* omega {lam {app{ {var 1} {var 1}}}})
(def* Omega {app {omega omega}})

;; church stuff

(def* TRUE {lam{lam {var 2} }})
(def* FALSE {lam{lam {var 1} }})

(def* PAIR {lam{lam{lam {app{ {app{ {var 1} {var 3} }} {var 2} }} }}})
(def* NIL {lam TRUE})

(def* ZERO {lam {lam {var 1}}})
(def* ONE {lam {lam {app{ {var 2} {var 1} }}}})
(def* TWO {lam {lam {app{ {var 2} {app{ {var 2} {var 1} }} }}}})
(def* THREE {lam {lam {app{ {var 2} {app{ {var 2} {app{ {var 2} {var 1} }}}} }}}})
(def* FOUR {lam {lam {app{ {var 2} {app{ {var 2} {app{ {var 2} {app{ {var 2} {var 1} }}}}}} }}}})
(def* FIVE {lam {lam {app{ {var 2} {app{ {var 2} {app{ {var 2} {app{ {var 2} {app{ {var 2} {var 1} }}}}}}}} }}}})

;; pairs

(def* FIRST {lam {app{ {var 1} TRUE }} })
(def* SECOND {lam {app{ {var 1} FALSE }} })
(def* NULL {lam {app{ {var 1} {lam{lam FALSE }} }} })

;; arithmetic

(def* SUCC {lam{lam{lam {app{ {var 2} {app{ {app{ {var 3}{var 2} }} {var 1} }} }} }}})
(def* PLUS {lam{lam{lam{lam {app{ {app{ {var 4} {var 2} }} {app{ {app{ {var 3}{var 2} }} {var 1} }} }} }}}})
(def* MULT {lam{lam {app{ {app{ {var 2} {app{ PLUS {var 1} }} }} ZERO }} }})
(def* POW {lam{lam {app{ {var 1} {var 2} }} }})

(def* SHIFINC {lam {app{ {app{ PAIR {app{ SECOND {var 1} }} }} {app{ SUCC {app{ SECOND {var 1} }} }} }} })
(def* PRED' {lam {app{ FIRST {app{ {app{ {var 1} SHIFINC }} {app{ {app{ PAIR ZERO }} ZERO }} }} }} })
(def* PRED {lam{lam{lam
{app{
  {app{
    {app{
      {var 3}
      {lam{lam
        {app{
          {var 1}
          {app{ {var 2} {var 4} }}
        }}
      }}
    }}
    {lam {var 2}}
  }}
  {lam {var 1}}
}} }}})
(def* SUB {lam{lam {app{ {app{ {var 1} PRED }} {var 2} }} }})

;; logic

(def* ISZERO {lam {app{ {app{ {var 1} {lam FALSE} }} TRUE }} })
(def* IF {lam{lam{lam {app{ {app{ {var 3} {var 2} }} {var 1} }} }}})
(def* NOT {lam {app{ {app{ {var 1} FALSE }} TRUE }} })
(def* AND {lam{lam {app{ {app{ {var 2} {var 1} }} {var 2} }} }})
(def* OR {lam{lam {app{ {app{ {var 2} {var 2} }} {var 1} }} }})

;; recursion

(def* Y {lam {app{
    {lam {app{ {var 2} {app{ {var 1} {var 1} }} }} }
    {lam {app{ {var 2} {app{ {var 1} {var 1} }} }} } }} })

(def* FAC {app{ Y FAC' }})
(def* FAC' {lam{lam
{app{
  {app{
    {app{ ISZERO {var 1} }}
    ONE
  }}
  {app{
    {app{ MULT {var 1} }}
    {app{ {var 2} {app{ PRED {var 1} }} }}
  }}
}} }})

(def* FAC2 {app{ FAC2' FAC2' }})
(def* FAC2' {lam
{app{
  {app{
    {app{ ISZERO {var 1} }}
    ONE
  }}
  Omega
  ;{app{
  ;  {app{ MULT {var 1} }}
  ;  {app{ {app{ {var 2} {var 2} }} {app{ PRED {var 1} }} }}
  ;}}
}} })
