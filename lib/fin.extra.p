import lib/fin.p
import lib/void.p
import lib/eq.p

def finZVoid
  : Fin Z -> Void
  = \x. (indFin {\i _. Eq Z i -> Void} z_neq_S (\_. z_neq_S) x) (Refl {_} {Z})
