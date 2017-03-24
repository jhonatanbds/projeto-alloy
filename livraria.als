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
// LEMBRAR: adicionar mais de um livro por vez
pred addLivroNoDrone[a:Armazem, l:Livro, c: Cliente, d: Drone, t,t':Time] {
	l in (a.livros).t
	l !in (d.carga).t
	l !in (c.livrosComprados).t
	(d.carga).t' = (d.carga).t + l
	(a.livros).t' = (a.livros).t - l
	
}

pred despachaDrone[a: Armazem, l: Livro,  d: Drone, c: Cliente, t,t':Time] {
	l in (a.livros).t
	l !in (d.carga).t
	l !in (c.livrosComprados).t
	(d.carga).t' = (d.carga).t + l
	(a.livros).t' = (a.livros).t - l
	d in (a.drones).t
	d !in (c.entrega).t
	(c.entrega).t' = c.(entrega.t) + d
	(a.drones).t' = (a.drones).t - d
}

pred entregarPedido[d: Drone, c: Cliente, l: Livro, t,t': Time] {
	d in c.(entrega.t) => l in c.(livrosComprados.t')
}

fact traces {
	init [first]
//	all pre: Time-last | let pos = pre.next |some a: Armazem, d: Drone, l:Livro, c: Cliente|
//		despachaDrone[a, l, d, c, pre, pos]

	all pre: Time-last | let pos = pre.next | all c: Cliente |
		impedeRoubo[c, pre, pos]

	all t: Time-last | all c: Cliente, d: Drone |
		despachou[t, d, c] => #d.(carga.t) > 0

	all t: Time-last | all a:Armazem, d: Drone |
		d in a.(drones.t) => #d.(carga.t) = 0

	all pre: Time-last | let pos = pre.next | all c: Cliente, a: Armazem, d: Drone |
		despachou[pre, d, c] => entregaERetorna[d, a, c, pre, pos]
}

pred despachou[t: Time, d: Drone, c: Cliente] {
	d in c.(entrega.t)
}

pred entregaERetorna[d: Drone, a: Armazem, c: Cliente, t,t':Time] {
	c.(livrosComprados.t') = c.(livrosComprados.t) + d.(carga.t)
	no c.(entrega.t')
	//a.(drones.t') = a.(drones.t) + d
}

pred impedeRoubo[c: Cliente, t,t': Time] {
	no c.(entrega.t) => #c.(livrosComprados.t) = #c.(livrosComprados.t')
}

pred init[t:Time] {
	some(Armazem.livros)
	all d: Drone, a: Armazem |  d in (a.drones).t
	all d: Drone | #d.(carga.t) = 0
	all c: Cliente| no c.(livrosComprados.t) and no c.(entrega.t)
}

fact FatosLivros {
	//Um livro comprado nao pode pertencer a mais de um cliente
	all l: Livro, c1,c2: Cliente, t: Time | (l in (c1.livrosComprados).t) and (l in (c2.livrosComprados).t) => c1 = c2

	//Um livro não pode estar no conteudo de dois drones
	all  t: Time, l: Livro | all d1,d2: Drone | ((l in d1.(carga.t)) and (l in d2.(carga.t))) => (d1 = d2)

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
	all d: Drone, t: Time | (#d.~(drones.t) > 0) or (#d.~(entrega.t) > 0)

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
