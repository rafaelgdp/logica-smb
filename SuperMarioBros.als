open util/time

enum EstadoMario {
    MarioBros,
    SuperMario,
    FireMario,
    MarioCapa,
    MarioMorto,
    MarioInvencivel
}

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
	Mario.estadoAtual = MarioBros
}

pred marioBrosColetaFlor[m, m':Mario, i:Item] {
    m.estadoAtual = MarioBros
    m.colidiuCom = Flor
    m'.estadoAtual = FireMario
}
pred show [] {
}

run show for 3
