(inh "prelude" nil cons ~1 ~2)

; in-place list reversal
(beq reverse reverse')
(grp
  (perm* (reverse reverse' l #)
         (`~1 [`loop `next] {{# #} l} reverse))

  (perm (loop [`reverse `next] {{r' r''} {~l l' l''}} ~r)
        (~l [`reverse' `next] {{~r r' r''} {l' l''}} loop))

  (perm (next [`reverse' `loop] {r {x xs}} `~2)
        (`~2 [`reverse `loop] {{x r} xs} next))

  (perm* (reverse' [`loop `next] {r' {# #}} `~1)
         (# r' `reverse reverse')))
