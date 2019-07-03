module marioBrosGame

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
	proximoEstado: EstadoMario, 
	colidiuCom:  EntidadeJogo
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
}

fact MarioMortoNaoRevive {
	all m: Mario | m.estadoAtual = MarioMorto => m.proximoEstado = MarioMorto
}

fact MarioColideComNadaContinuaOMesmo {
	all m:Mario | (m.colidiuCom = Nada) => (m.estadoAtual = m.proximoEstado)
}

fact MarioColideComInimigo{
	-- unica maneira de morrer eh se for mario bros e tocar no inimigo ou se ja estava morto
	all m:Mario |  (m.proximoEstado = MarioMorto) <=> ((m.estadoAtual = MarioBros && marioLevaDano[m]) || (m.estadoAtual = MarioMorto))
}

fact MarioInvencivelCondicoes {
	all m:Mario | (m.proximoEstado = MarioInvencivel) <=> ((m.estadoAtual != MarioMorto && marioColetaEstrela[m]) ||
																			    (m.estadoAtual = MarioInvencivel && m.colidiuCom = Nada || marioColetaCogumelo[m] || marioLevaDano[m]))
} 

fact FireMarioCondicoes {
	all m:Mario | m.proximoEstado = FireMario <=> ((m.estadoAtual != MarioMorto && marioColetaFlor[m]) ||
																		(m.estadoAtual = FireMario && m.colidiuCom = Nada))
}

fact MarioCapaCondicoes{
	all m:Mario | m.proximoEstado = MarioCapa <=> ((m.estadoAtual != MarioMorto && marioColetaPena[m]) ||
																		(m.estadoAtual = MarioCapa  && m.colidiuCom = Nada || marioColetaCogumelo[m]))
}

fact SuperMarioCondicoes{
	all m:Mario | (m.proximoEstado = SuperMario) <=> ((m.estadoAtual = MarioBros && m.colidiuCom = Cogumelo) ||
																		(m.estadoAtual = SuperMario && m.colidiuCom = Nada) ||
																		(m.estadoAtual = MarioCapa || m.estadoAtual = FireMario && m.colidiuCom = Inimigo))
}

fact MarioBrosCondicoes{
	all m:Mario | (m.proximoEstado = MarioBros) <=> (((m.estadoAtual = SuperMario || m.estadoAtual = FireMario || m.estadoAtual = MarioCapa) && (marioLevaDano[m])) ||
																		(m.estadoAtual = MarioBros && m.colidiuCom = Nada))
}

fact SuperMarioColideInimigoEDiminui{
	all m:Mario | (m.estadoAtual = SuperMario && marioLevaDano[m]) => m.proximoEstado = MarioBros
}

pred marioLevaDano[m:Mario] {
	m.colidiuCom = Inimigo
}

pred marioColetaCogumelo[m:Mario] {
	m.colidiuCom = Cogumelo
}

pred marioColetaFlor[m:Mario] {
	m.colidiuCom = Flor
}

pred marioColetaPena[m:Mario] {
	m.colidiuCom = Pena
}

pred marioColetaEstrela[m:Mario] {
	m.colidiuCom = Estrela
}

pred testeMarioColetaCogumeloENaoMuda[] {
	all m:Mario | (m.estadoAtual = FireMario || m.estadoAtual = SuperMario || m.estadoAtual = MarioCapa || m.estadoAtual = MarioInvencivel && m.colidiuCom = Cogumelo) => m.proximoEstado = m.estadoAtual
}

pred testeMarioEstrelaConsistente [] {
	all m:Mario | m.colidiuCom = Estrela => (m.proximoEstado != MarioCapa && m.proximoEstado != FireMario &&
															m.proximoEstado != SuperMario && m.proximoEstado != MarioBros)
}

pred testeMarioCapaConsistente [] {
	all m:Mario | (m.colidiuCom = Pena && m.estadoAtual != MarioMorto) => (m.proximoEstado != MarioInvencivel && m.proximoEstado != MarioBros &&
														m.proximoEstado != FireMario && m.proximoEstado != SuperMario)
}


assert testeGeral {
	testeMarioColetaCogumeloENaoMuda and
	testeMarioEstrelaConsistente and
	testeMarioCapaConsistente
}

check testeGeral

pred show [] {
}

run show for 3
