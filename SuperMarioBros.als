module marioBrosGame

open util/ordering[Time]

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
	estadoAtual: EstadoMario one -> Time,
	colidiuCom:  EntidadeJogo  one -> Time //Ultima colisão
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
	(Mario.estadoAtual).t = MarioBros
	(Mario.colidiuCom).t = Nada
}

fact{
	morto[Mario, Time] && fire[Mario, Time] && pena[Mario, Time] && invencivel[Mario, Time] &&  super[Mario, Time] && bros[Mario, Time]
}

pred morto[mario:Mario, t:Time]{
	(mario.estadoAtual.t = MarioMorto) => (mario.colidiuCom.t = Inimigo)
}

fact MarioColideComInimigo{
	all m:Mario |  (m.proximoEstado = MarioMorto) => ((m.estadoAtual = MarioBros && m.colidiuCom = Inimigo) || (m.estadoAtual = MarioMorto))
}

fact MarioInvencivelCondicoes{
	all m:Mario | (m.proximoEstado = MarioInvencivel) => (m.estadoAtual = MarioInvencivel && (m.colidiuCom = Cogumelo || m.colidiuCom = Estrela || m.colidiuCom = Inimigo))
} 

fact MarioColetaFor{
	all m:Mario | m.proximoEstado = FireMario => ((m.estadoAtual = MarioBros || m.estadoAtual = MarioInvencivel) && m.colidiuCom = Flor)
}

fact MarioColetaCogumelo{
	all m:Mario | m.proximoEstado = SuperMario => (m.estadoAtual = MarioBros && m.colidiuCom = Cogumelo)
}

fact MarioColetaPena{
	all m:Mario | m.proximoEstado = MarioCapa => ((m.estadoAtual = MarioBros || m.estadoAtual = MarioInvencivel) && m.colidiuCom = Pena)
}

fact MarioColetaEstrela{
	all m:Mario | m.proximoEstado = MarioInvencivel => (m.estadoAtual = MarioBros && m.colidiuCom = Estrela)
}

fact SuperMarioColideInimigo{
	all m:Mario | m.proximoEstado = MarioBros => (m.estadoAtual = SuperMario && m.colidiuCom = Inimigo)
}

fact SuperMarioColetaCogumelo{
	all m:Mario | m.proximoEstado = m.estadoAtual => (m.estadoAtual = SuperMario && m.colidiuCom = Cogumelo)
}

fact SuperMarioColetaPena{
	all m:Mario | m.proximoEstado = MarioCapa => (m.estadoAtual = SuperMario && m.colidiuCom = Pena)
}

fact SuperMarioColetaFlor{
	all m:Mario | m.proximoEstado = FireMario => (m.estadoAtual = SuperMario && m.colidiuCom = Flor)
}

fact SuperMarioColetaEstrela{
	all m:Mario | m.proximoEstado = MarioInvencivel => (m.estadoAtual = SuperMario && m.colidiuCom = Estrela)
}

fact FireMarioColetaCogumeloOuFlor{
	all m:Mario | m.proximoEstado = m.estadoAtual => (m.estadoAtual = FireMario && (m.colidiuCom = Cogumelo || m.colidiuCom = Flor))
}

fact FireMarioColetaPena{
	all m:Mario | m.proximoEstado = MarioCapa => (m.estadoAtual = FireMario && m.colidiuCom = Pena)
}

fact FireMarioColetaEstrela{
	all m:Mario | m.proximoEstado = MarioInvencivel => (m.estadoAtual = FireMario && m.colidiuCom = Estrela)
}

fact MarioCapaColetaCogumeloOuPena{
	all m:Mario | m.proximoEstado = m.estadoAtual => (m.estadoAtual = FireMario && (m.colidiuCom = Cogumelo || m.colidiuCom = Pena))
}

fact VoltaSuperMario{
	all m:Mario | m.proximoEstado = SuperMario => ((m.estadoAtual = FireMario || m.estadoAtual = MarioCapa) && m.colidiuCom = Inimigo)
}

fact MarioCapaColetaFlor{
	all m:Mario | m.proximoEstado = FireMario => (m.estadoAtual = MarioCapa && m.colidiuCom = Flor)
}

fact MarioCapaColetaEstrela{
	all m:Mario | m.proximoEstado = MarioInvencivel => (m.estadoAtual = MarioCapa && m.colidiuCom = Estrela)
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

pred invencivel [mario:Mario, t:Time]{
		mario.estadoAtual.t = MarioInvencivel => (mario.colidiuCom.t = Estrela || mario.colidiuCom.t = Cogumelo || mario.colidiuCom.t = Nada ||  mario.colidiuCom.t = Inimigo)
}

pred super[mario:Mario, t:Time]{
		mario.estadoAtual.t = SuperMario => (mario.colidiuCom.t = Cogumelo || mario.colidiuCom.t = Nada || mario.colidiuCom.t = Inimigo) 
}

pred bros[mario:Mario, t:Time]{
		mario.estadoAtual.t = MarioBros => (mario.colidiuCom.t = Nada || mario.colidiuCom.t = Inimigo) 
}


pred show [] {
}

run show for 5
