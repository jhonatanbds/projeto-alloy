module livraria

open util/ordering[Time] as to
sig Time {} 

one sig Livraria{
	armaze: Armazem,
	clientes: set Cliente
}

one sig Armazem{
	livros: set Livro->Time,
	drones: set Drone->Time
}

abstract sig Drone {}

sig DroneComum extends Drone{
//	clientesComuns: set ClienteComum  ??
}

sig DroneEspecial extends Drone {
//	clientesConveniados: set ClienteConveniado  ??
}

abstract sig Cliente {
	livrosComprados: set Livro->Time
}

sig ClienteComum extends Cliente {}

sig ClienteConveniado extends Cliente {}

sig Livro {} 

abstract sig Pedido {}

sig PedidoComum extends Pedido {}

sig PedidoEspecial extends Pedido {}

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

fact fatos {
	
	// Define que um livro não pode pertencer ao armazem e
	// a um cliente ao mesmo tempo
	all L: Livro, c: Cliente, a: Armazem, t: Time |
		(L in (a.livros).t and L !in (c.livrosComprados).t) or
		(L !in (a.livros).t and L in (c.livrosComprados).t)
	
	//todo drone deve pertencer ao armazem
	all d: Drone, a: Armazem, t: Time | d in (a.drones).t 

	//todo livro deve pertencer ao armazem ou a um cliente
	all c1, c2: Cliente, t: Time | c1 != c2 => 
		#((c1.livrosComprados).t & (c2.livrosComprados).t) = 0

	#DroneEspecial = 2
	#DroneComum = 3
	#livros > 0 //acho que dever ser >= 0
	#Time <= 5
	#Cliente > 0
	#livrosComprados >= 0

		
	
}

pred init [t: Time] {
	no (Cliente.livrosComprados).t
}

pred show[]{}

run show for 5
