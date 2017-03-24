module livraria
open util/ordering[Time]

sig Time{}

one sig Livraria{
	armazem: Armazem,
	clientes: set Cliente
}

one sig Armazem{
	livros: set Livro->Time,
	drones: set Drone->Time
}

abstract sig Drone {
	carga: set Livro->Time
}

sig DroneComum extends Drone{
}

sig DroneEspecial extends Drone {
}

abstract sig Cliente {
	entrega: set Drone->Time,
	livrosComprados: set Livro->Time
}

sig ClienteComum extends Cliente {}

sig ClienteConveniado extends Cliente {}

sig Livro {} 


// Operação de compra de livros: O livro sai do armazem para o cliente
pred compraLivro[a:Armazem, l:Livro, c:Cliente, t,t':Time] {
	l in (a.livros).t
	l !in (c.livrosComprados).t
	(c.livrosComprados).t' = (c.livrosComprados).t + l
	(a.livros).t' = (a.livros).t - l
}

fact traces {
	init [first]
	all pre: Time-last | let pos = pre.next |
	some a: Armazem, c: Cliente, l:Livro |
		compraLivro[a, l, c, pre, pos]
}

pred addLivroDrone[a: Armazem, d:Drone, li:Livro, t,t':Time]{
	li in (a.livros).t
	d in (a.drones).t
	#(d.carga).t = 0
	(a.livros).t' = (a.livros).t - li
	(a.drones).t' = (a.drones).t - d
	(d.carga).t' = (d.carga).t + li
}

pred init[t:Time]{
	some(Armazem.livros)
	no(Drone.carga).t
	
}

fact traces{
	init[first]
	all pre:Time - last | let pos = pre.next |
		some a:Armazem, d:Drone, li: set Livro |
		addLivroDrone[a,d,li,pre,pos]
}

fact FatosLivros {
	//Um livro comprado nao pode pertencer a mais de um cliente
	all l: Livro, c1,c2: Cliente, t: Time | (l in (c1.livrosComprados).t) and (l in (c2.livrosComprados).t) => c1 = c2

	//Um livro não pode estar no conteudo de dois drones
	all l: Livro, d1,d2: Drone , t: Time| (l in (d1.carga).t) and (l in (d2.carga).t) => d1 = d2

	//Livros estão com clientes, no armazém ou na carga de um drone
	all l: Livro, t: Time | ((#l.~(livrosComprados.t) > 0) iff not (#l.~(livros.t) > 0) iff not (#l.~(carga.t) > 0)) iff not
			    ((#l.~(livrosComprados.t) > 0) and (#l.~(livros.t) > 0) and (#l.~(carga.t) > 0))

}

fact FatosDrones {
	//Drones comuns só podem carregar até 3 livros
	#DroneComum.carga <= 3

	//Drones especiais só podem carregar até 5 livros
	#DroneEspecial.carga <= 5

	//Um drone não pode fazer duas entregas ao mesmo tempo
	all d: Drone, c1, c2: Cliente, t: Time | (d in (c1.entrega).t) and (d in (c2.entrega).t) => c1 = c2

	//Drones ou estão com clientes ou no armazem
	all d: Drone, t: Time | (#d.~(drones.t) > 0) iff not (#d.~(entrega.t) > 0)
	
	//Drones não podem fazer entregas vazias
	all c: Cliente, t: Time | #((c.entrega).t).carga > 0

	// Drones no armazem nao possuem carga
	all a: Armazem, t: Time | #((a.drones).t).carga = 0

	#DroneEspecial = 2
	#DroneComum = 3	
}



fact FatosClientes {
	

	//Todo cliente é um cliente da livraria
	all c:Cliente, livraria:Livraria | c in (livraria.clientes)

	//Clientes comuns só podem usar drones comuns, e clientes conveniados, drones especiais
	all c: ClienteComum, t: Time | (c.entrega).t in DroneComum	
	all c: ClienteConveniado, t: Time| (c.entrega).t in DroneEspecial	
}


pred show[]{}

run show for 10
