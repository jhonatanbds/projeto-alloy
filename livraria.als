module livraria

open util/ordering[Time] as to
sig Time {} 

sig Armazem{
	livros: set Livro->Time,
	drones: set Drone->Time
}

abstract sig Drone {}

sig DroneComum extends Drone{
	clientesComuns: set ClienteComum
}

sig DroneEspecial extends Drone {
	clientesConveniados: set ClienteConveniado
}

abstract sig Cliente {
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

fact fatos {
	
	// Define que um livro não pode pertencer ao armazem e
	// a um cliente ao mesmo tempo
	all l: Livro, c: Cliente, a: Armazem, t: Time |
		(l in (a.livros).t and l !in (c.livrosComprados).t) or
		(l !in (a.livros).t and l in (c.livrosComprados).t)

	#livros > 0
	#Armazem = 1
	#DroneEspecial = 2 && #DroneComum = 3
	#Time <= 5
	#Cliente > 0
	
}

pred init [t: Time] {
	no (Cliente.livrosComprados).t
}

pred show[]{}

run show for 5
