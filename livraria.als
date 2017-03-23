module livraria
open util/ordering[Time]

sig Time{}

one sig Livraria{
	armazem: Armazem,
	clientes: some Cliente
}

one sig Armazem{
	livros: set Livro -> Time,
	drones: set Drone ->Time
}

abstract sig Drone {
	entrega: set Livro -> Time
}

sig DroneComum extends Drone{}

sig DroneEspecial extends Drone {}

abstract sig Cliente {
	livrosComprados: set Livro ->Time
}

sig ClienteComum extends Cliente {

	entregaComum: set DroneComum ->Time
	
}

sig ClienteConveniado extends Cliente {
	
	entregaEspecial: set DroneEspecial ->Time
	
}

sig Livro {} 


// Operação de compra de livros: O livro sai do armazem para o cliente
/*pred compraLivro[a:Armazem, l:Livro, c:Cliente, t,t':Time] {
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
}*/

pred addLivroDrone[a: Armazem, d:Drone, li:Livro, t,t':Time]{
	li in (a.livros).t
	d in (a.drones).t
	#(d.entrega).t = 0
	(a.livros).t' = (a.livros).t - li
	(a.drones).t' = (a.drones).t - d
	(d.entrega).t' = (d.entrega).t + li

}

pred compraLivro[d:Drone, li:Livro, c:Cliente, t,t':Time]{

	

}

pred init[t:Time]{
	some(Armazem.livros)
	no(Drone.entrega).t
	
}

fact traces{
	init[first]
	all pre:Time - last | let pos = pre.next |
		some a:Armazem, d:Drone, li: set Livro |
		addLivroDrone[a,d,li,pre,pos]
}

fact fatos {
	
	//todo drone deve pertencer ao armazem ou estar à caminho de um cliente
	//all d: Drone,cc: ClienteComum, ce:ClienteConveniado, a: Armazem | (d in a.drones and d !in cc.entregaComum and d !in ce.entregaEspecial) or
		//(d !in a.drones and d in cc.entregaComum and d !in ce.entregaEspecial) or (d !in a.drones and d !in cc.entregaComum and d in ce.entregaEspecial)

	//Drones só podem estar à caminho de um cliente por vez
	//all d:Drone, t:Time | #(d.~entregaComum) <= 1 and #(d.~entregaEspecial) <= 1
	
	//A qualquer tempo, um livro está no armazém, ou está à caminho do cliente ou está com o cliente
	all livro:Livro, a:Armazem,d:Drone,c:Cliente, t:Time|
		(livro in (a.livros).t  and livro !in (d.entrega).t and livro !in (c.livrosComprados).t) or 
		(livro in (d.entrega).t and livro !in (a.livros).t and livro !in (c.livrosComprados).t) or
 		(livro in(c.livrosComprados).t  and livro !in (d.entrega).t and livro !in (a.livros).t)

	//O armazém e o cliente não possuem os mesmos livros
	all a:Armazem, c:Cliente, t:Time|
		#((a.livros).t & (c.livrosComprados).t) = 0

//	all d:Drone, a:Armazem, c:Cliente, t:Time|
	//	#(      ((d.entrega).t & (a.livros).t)     & ((d.entrega).t &(c.livrosComprados).t)  & ((a.livros).t & (c.livrosComprados).t)  ) = 0

	//Drones comuns só podem carregar até 3 livros
	all dc:DroneComum| #dc.entrega <= 3

	//Drones especiais só podem carregar até 5 livros
	all de:DroneEspecial| #de.entrega <= 5

	//um livro comprado nao pode pertencer a mais de um cliente
	all c1, c2: Cliente | c1 != c2 => 
		#(c1.livrosComprados & c2.livrosComprados) = 0

	//Um livro não pode estar na carga de dois drones
	all d1,d2: Drone | d1 != d2 => 
		#(d1.entrega & d2.entrega) = 0

	//Livros estão com clientes, no armazém ou na carga de um drone
	//all livro:Livro, arm:Armazem, cli:Cliente, dro:Drone | (livro  !in ((arm.livros & cli.livrosComprados)+
		// (arm.livros & dro.entrega)+ (dro.entrega & cli.livrosComprados)))

	//Todo cliente é um cliente da livraria
	all c:Cliente, livraria:Livraria | c in livraria.clientes

	//Os drones não podem estar no armazém e à caminho de um cliente ao mesmo tempo
	//all cc: ClienteComum, ce:ClienteConveniado, a: Armazem | #(cc.entregaComum & a.drones) = 0 and #(ce.entregaEspecial & a.drones) =0
	
	//Existem dois drones especiais
	//#DroneEspecial = 2
	//Existem três drones comuns
	//#DroneComum = 3
	#ClienteComum.entregaComum < 2	
	#ClienteConveniado.entregaEspecial < 2	
}

pred show[]{}

run show for 10
