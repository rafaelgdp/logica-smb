open util/ordering[State]

open util/integer

enum EstadoMario {
    MarioBros,
    SuperMario,
    FireMario,
    MarioCapa,
    MarioMorto,
    MarioInvencivel
}

enum Bool {False, True}

sig Mario {
    estadoAtual: EstadoMario,
    colidiuCom: EntidadeJogo
}

abstract sig EntidadeJogo {}

abstract sig Item extends EntidadeJogo {}
sig Flor extends Item {}
sig Pena extends Item {}
sig Cogumelo extends Item {}
sig Estrela extends Item {}

sig Inimigo extends EntidadeJogo {}
sig Nada extends EntidadeJogo {}

pred init[t:Time] {
    (Mario.estadoAtual).t = EstadoMario.MarioBros
}

pred coletarItem[m:Mario, i:Item, t,t':Time] {
    (m.estadoAtual).t = EstadoMario.MarioBros
    (m.colidiuCom).t = Flor
    (m.estadoAtual).t' = EstadoMario.FireMario
}


pred show [] {
}

run show for 3
