module question where

CN = Set

postulate
  woman human : CN
  jane : woman

postulate
  wh : woman → human

record Coercion {a} (x y : Set a) : Set a where
  constructor ⌞_⌟
  field coe : x → y

instance
  wac = ⌞ wh ⌟

explicitCoercion : {{woman -> human}} → woman → human
explicitCoercion {{wac}} w = wh w

instanceCoercion : {{woman -> human}} → woman → human
instanceCoercion {{wac}} w = wac w
