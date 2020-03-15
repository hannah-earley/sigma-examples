(inh "prelude" nil cons)

; in-place list reversal
(beq reverse reverse')
(grp
  (perm* (reverse `reverse' l #)
         (`nil [`loop `next] {{# #} l} reverse))

  (perm (loop [`reverse `next] {{r' r''} {~l l' l''}} ~r)
        (~l [`reverse' `next] {{~r r' r''} {l' l''}} loop))

  (perm (next [`reverse' `loop] {r {x xs}} `cons)
        (`cons [`reverse `loop] {{x r} xs} next))

  (perm* (reverse' [`loop `next] {r' {# #}} `nil)
         (# r' `reverse reverse')))
