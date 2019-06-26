open util/ordering[Time] as to

sig Time{}

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
	proximoEstado:EstadoMario,
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

fact invencivel{
	Mario.estadoAtual = MarioInvencivel && (Mario.colidiuCom != Flor && Mario.colidiuCom != Pena)
	Mario.proximoEstado = MarioInvencivel
}
fact morto{
	Mario.proximoEstado = MarioMorto => (Mario.estadoAtual = MarioMorto || MarioMorre[Mario])

}

pred init[t:Time] {
	Mario.estadoAtual = MarioBros
	Mario.colidiuCom = Nada
	Mario.proximoEstado = MarioBros
}

pred MarioMorre [m:Mario]{
	m.estadoAtual = MarioBros
	m.colidiuCom = Inimigo 
	m.proximoEstado = MarioMorto
}


pred marioColetaFlor[m:Mario] {
	m.colidiuCom = Flor
	m.estadoAtual != MarioMorto
	
	m.proximoEstado= FireMario
}

pred marioColetaPena[m:Mario] {
	m.colidiuCom = Pena
	m.estadoAtual != MarioMorto
	
	m.proximoEstado= MarioCapa
}

pred marioColetaEstrela[m:Mario] {
	m.colidiuCom = Estrela
	m.estadoAtual != MarioMorto
	m.proximoEstado = MarioInvencivel
}

pred marioColetaCogumeloENaoMuda[m:Mario] {
	m.estadoAtual = FireMario || m.estadoAtual = SuperMario || m.estadoAtual = MarioCapa || m.estadoAtual = MarioInvencivel
	m.colidiuCom = Cogumelo
	m.proximoEstado = m.estadoAtual
}


pred show [] {
}

run show for 10
