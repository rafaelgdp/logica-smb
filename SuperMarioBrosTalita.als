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

//Geral

fact MarioMortoNaoRevive {
	all m: Mario | m.estadoAtual = MarioMorto => m.proximoEstado = MarioMorto
}

fact MarioColideComNadaContinuaOMesmo {
	all m:Mario | (m.colidiuCom = Nada) => (m.estadoAtual = m.proximoEstado)
}

fact VoltaSuperMario{
	all m:Mario |   ((m.estadoAtual = FireMario || m.estadoAtual = MarioCapa) && m.colidiuCom = Inimigo) => m.proximoEstado = SuperMario
}

fact MorteDoMario{
	all m:Mario |(m.proximoEstado = MarioMorto) <=> (m.estadoAtual = MarioMorto || (m.estadoAtual = MarioBros && m.colidiuCom = Inimigo))
}


//Mario Bros

fact MarioColideComInimigo{
	all m:Mario |  ((m.estadoAtual = MarioBros && m.colidiuCom = Inimigo) || (m.estadoAtual = MarioMorto)) => (m.proximoEstado = MarioMorto)
}

fact MarioInvencivelCondicoes{
	all m:Mario | (m.estadoAtual = MarioInvencivel && (m.colidiuCom = Cogumelo || m.colidiuCom = Estrela || m.colidiuCom = Inimigo)) => (m.proximoEstado = MarioInvencivel)
} 

fact MarioColetaFlor{
	all m:Mario |  ((m.estadoAtual = MarioBros || m.estadoAtual = MarioInvencivel) && m.colidiuCom = Flor) => m.proximoEstado = FireMario
}

fact MarioColetaCogumelo{
	all m:Mario | (m.estadoAtual = MarioBros && m.colidiuCom = Cogumelo) => m.proximoEstado = SuperMario
}

fact MarioColetaPena{
	all m:Mario | ((m.estadoAtual = MarioBros || m.estadoAtual = MarioInvencivel) && m.colidiuCom = Pena) => m.proximoEstado = MarioCapa
}

fact MarioColetaEstrela{
	all m:Mario |  (m.estadoAtual = MarioBros && m.colidiuCom = Estrela) => m.proximoEstado = MarioInvencivel
}


//Super Mario
fact SuperMarioColideInimigo{
	all m:Mario |  (m.estadoAtual = SuperMario && m.colidiuCom = Inimigo) => m.proximoEstado = MarioBros
}

fact SuperMarioColetaCogumelo{
	all m:Mario |  (m.estadoAtual = SuperMario && m.colidiuCom = Cogumelo) => m.proximoEstado = SuperMario
}

fact SuperMarioColetaPena{
	all m:Mario | (m.estadoAtual = SuperMario && m.colidiuCom = Pena) => m.proximoEstado = MarioCapa
}

fact SuperMarioColetaFlor{
	all m:Mario |  (m.estadoAtual = SuperMario && m.colidiuCom = Flor) => m.proximoEstado = FireMario
}

fact SuperMarioColetaEstrela{
	all m:Mario | (m.estadoAtual = SuperMario && m.colidiuCom = Estrela) => m.proximoEstado = MarioInvencivel
}


//Fire Mario

fact FireMarioColetaCogumeloOuFlor{
	all m:Mario | (m.estadoAtual = FireMario && (m.colidiuCom = Cogumelo || m.colidiuCom = Flor)) => m.proximoEstado = FireMario
}

fact FireMarioColetaPena{
	all m:Mario |  (m.estadoAtual = FireMario && m.colidiuCom = Pena) => m.proximoEstado = MarioCapa
}

fact FireMarioColetaEstrela{
	all m:Mario |  (m.estadoAtual = FireMario && m.colidiuCom = Estrela) => m.proximoEstado = MarioInvencivel
}



//Mario Capa

fact MarioCapaColetaCogumeloOuPena{
	all m:Mario | (m.estadoAtual = MarioCapa && (m.colidiuCom = Cogumelo || m.colidiuCom = Pena)) => m.proximoEstado = MarioCapa
}

fact MarioCapaColetaFlor{
	all m:Mario | (m.estadoAtual = MarioCapa && m.colidiuCom = Flor) => m.proximoEstado = FireMario
}

fact MarioCapaColetaEstrela{
	all m:Mario |  (m.estadoAtual = MarioCapa && m.colidiuCom = Estrela) => m.proximoEstado = MarioInvencivel
}


//Mario Invencível

fact MarioNaoPerdeInvencibilidade{
	all m:Mario | (m.estadoAtual = MarioInvencivel && (m.colidiuCom = Inimigo || m.colidiuCom = Cogumelo || m.colidiuCom = Estrela)) => m.proximoEstado = MarioInvencivel
}

fact MarioInvencivelColideComFlor{
	all m:Mario | (m.estadoAtual = MarioInvencivel && m.colidiuCom = Flor) => m.proximoEstado = FireMario
}
fact MarioInvencivelColideComPena{
	all m:Mario | (m.estadoAtual = MarioInvencivel && m.colidiuCom = Pena) => m.proximoEstado = MarioCapa
}
fact MarioInvencivelColideComQualquerOutraCoisa{
	all m:Mario | (m.estadoAtual = MarioInvencivel && (m.colidiuCom != Pena && m.colidiuCom != Flor)) => m.proximoEstado = MarioInvencivel
}




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



//TESTES

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

pred testeFireMarioConsistente[]{
	all m:Mario | (m.estadoAtual = FireMario && (m.colidiuCom = Flor || m.colidiuCom = Cogumelo)) => m.proximoEstado = FireMario
}



assert testeGeral {
	testeMarioColetaCogumeloENaoMuda and
	testeMarioEstrelaConsistente and
	testeMarioCapaConsistente and 
	testeFireMarioConsistente
}



pred show [] {
}

run show for 5
