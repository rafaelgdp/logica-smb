open util/ordering[State]

open util/integer

enum Bool {False, True}

abstract sig Mario {}

sig MarioBros extends Mario {}
sig SuperMario extends Mario {}
sig FireMario extends Mario {}
sig MarioCapa extends Mario {}
sig MarioMorto extends Mario {}
sig MarioInvencivel extends Mario {}

sig Item {}
sig Flor extends Item {}
sig Pena extends Item {}
sig Cogumelo extends Item {}
sig Estrela extends Item {}
sig Inimigo extends Item {}

pred show[] {

}

run show for 3
