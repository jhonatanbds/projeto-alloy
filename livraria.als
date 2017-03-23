module livraria

one sig Livraria{
	armazem: Armazem,
	clientes: some Cliente
}

one sig Armazem{
	livros: set Livro,
	drones: set Drone
}

abstract sig Drone {
	entrega: set Livro
}

sig DroneComum extends Drone{}

sig DroneEspecial extends Drone {}

abstract sig Cliente {
	livrosComprados: set Livro
}

sig ClienteComum extends Cliente {

	entregaComum: lone DroneComum
	
}

sig ClienteConveniado extends Cliente {
	
	entregaEspecial: lone DroneEspecial
	
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

fact fatos {
	
	//todo drone deve pertencer ao armazem ou estar à caminho de um cliente
	all d: Drone,cc: ClienteComum, ce:ClienteConveniado, a: Armazem | (d in a.drones and !d in cc.entregaComum and !d in ce.entregaEspecial) or
		(!d in a.drones and d in cc.entregaComum and !d in ce.entregaEspecial)or (!d in a.drones and !d in cc.entregaComum and d in ce.entregaEspecial)

	//Drones só podem estar à caminho de um cliente por vez
	all d:Drone | #(d.~entregaComum) <= 1 and #(d.~entregaEspecial) <= 1

	//Drones comuns só podem carregar até 3 livros
	all dc:DroneComum| #dc.entrega <= 3

	//Drones especiais só podem carregar até 5 livros
	all de:DroneEspecial| #de.entrega <= 5

	//um livro comprado nao pode pertencer a mais de um cliente
	all c1, c2: Cliente | c1 != c2 => 
		#(c1.livrosComprados & c2.livrosComprados) = 0

	//Um livro não pode estar no conteudo de dois pedidos
	all d1,d2: Drone | d1 != d2 => 
		#(d1.entrega & d2.entrega) = 0

	//Livros estão com clientes, no armazém ou na carga de um drone
	all livro:Livro, arm:Armazem, cli:Cliente, dro:Drone | (livro  !in ((arm.livros & cli.livrosComprados)+
		 (arm.livros & dro.entrega)+ (dro.entrega & cli.livrosComprados)))

	//Todo cliente é um cliente da livraria
	all c:Cliente, livraria:Livraria | c in livraria.clientes

	//Os drones não podem estar no armazém e à caminho de um cliente ao mesmo tempo
	all cc: ClienteComum, ce:ClienteConveniado, a: Armazem | #(cc.entregaComum & a.drones) = 0 and #(ce.entregaEspecial & a.drones) =0

	#DroneEspecial = 2
	#DroneComum = 3	
}

pred show[]{}

run show for 15
