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

pred fire[mario:Mario, t:Time]{
	mario.estadoAtual.t = FireMario => (mario.colidiuCom.t = Flor || mario.colidiuCom.t = Cogumelo || mario.colidiuCom.t = Nada)
}

pred pena[mario:Mario, t:Time]{
		mario.estadoAtual.t = MarioCapa => (mario.colidiuCom.t = Pena || mario.colidiuCom.t = Cogumelo || mario.colidiuCom.t = Nada)
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

run show for 2
