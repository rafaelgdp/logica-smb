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

pred init[m:Mario] {
	m.estadoAtual = MarioBros
	m.proximoEstado = MarioBros
	m.colidiuCom = Nada
}

fact MarioMortoNaoRevive {
	all m: Mario | m.estadoAtual = MarioMorto => m.proximoEstado = MarioMorto
}

fact MarioColideComNadaContinuaOMesmo {
	all m:Mario | (m.colidiuCom = Nada) => (m.estadoAtual = m.proximoEstado)
}

fact MarioColideComInimigo{
	all m:Mario |  (m.proximoEstado = MarioMorto) => ((m.estadoAtual = MarioBros && m.colidiuCom = Inimigo) || (m.estadoAtual = MarioMorto))
}

//fact EstadosPossiveis{
//	all m:Mario | 	marioColetaCogumelo[m] && marioColetaFlor[m] && marioColetaPena[m] &&  marioColetaEstrela[m]
//}

pred marioColetaCogumelo[m:Mario] {
	m.colidiuCom = Cogumelo
	m.proximoEstado = SuperMario
}

pred marioColetaFlor[m:Mario] {
	m.colidiuCom = Flor
	m.proximoEstado = FireMario
}

pred marioColetaPena[m:Mario] {
	m.estadoAtual != MarioMorto
	m.colidiuCom = Pena
	m.proximoEstado = MarioCapa
}

pred marioColetaEstrela[m:Mario] {
	m.colidiuCom = Estrela
	m.proximoEstado = MarioInvencivel
}

pred marioColetaCogumeloENaoMuda[m:Mario] {
	m.estadoAtual = FireMario || m.estadoAtual = SuperMario || m.estadoAtual = MarioCapa || m.estadoAtual = MarioInvencivel
	m.colidiuCom = Cogumelo
	m.proximoEstado = m.estadoAtual
}

pred show [] {
}

run show for 3
