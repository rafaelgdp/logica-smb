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
	colidiuCom: EntidadeJogo //Ultima colisão
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
	Mario.colidiuCom = Nada
}


fact morto{
	(Mario.estadoAtual = MarioMorto) => (Mario.colidiuCom = Inimigo)
}

fact fire{
	Mario.estadoAtual = FireMario => (Mario.colidiuCom = Flor || Mario.colidiuCom = Cogumelo || Mario.colidiuCom = Nada)
}

fact pena{
		Mario.estadoAtual = MarioCapa => (Mario.colidiuCom = Pena || Mario.colidiuCom = Cogumelo || Mario.colidiuCom = Nada)
}

fact invencivel {
		Mario.estadoAtual = MarioInvencivel => (Mario.colidiuCom = Estrela || Mario.colidiuCom = Cogumelo || Mario.colidiuCom = Nada ||  Mario.colidiuCom = Inimigo)
}

fact super{
		Mario.estadoAtual = SuperMario => (Mario.colidiuCom = Cogumelo || Mario.colidiuCom = Nada || Mario.colidiuCom = Inimigo) 
}

fact bros{
		Mario.estadoAtual = MarioBros => (Mario.colidiuCom = Nada || Mario.colidiuCom = Inimigo) 
}


pred show [] {
}

run show for 3
