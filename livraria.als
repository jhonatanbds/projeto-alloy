module livraria

one sig Livraria{
	armaze: Armazem,
	clientes: some Cliente
}

one sig Armazem{
	livros: set Livro,
	drones: set Drone
}

abstract sig Drone {
	entrega: lone Pedido
}

sig DroneComum extends Drone{}

sig DroneEspecial extends Drone {}

abstract sig Cliente {
	livrosComprados: set Livro
}

sig ClienteComum extends Cliente {
	pedidoComum: lone PedidoComum
}

sig ClienteConveniado extends Cliente {
	pedidoEspecial: lone PedidoEspecial
}

sig Livro {} 

abstract sig Pedido {
	conteudo: set Livro
}

sig PedidoComum extends Pedido {
}

sig PedidoEspecial extends Pedido {
}

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
	
	//todo drone deve pertencer ao armazem
	all d: Drone, a: Armazem | d in a.drones

	all p: Pedido | one p.~entrega
	all p:Pedido | one p.~pedidoComum or one p.~pedidoEspecial
	all dc:DroneComum| dc.entrega = PedidoComum
	all de:DroneEspecial| de.entrega = PedidoEspecial

	//um livro comprado nao pode pertencer a mais de um cliente
	all c1, c2: Cliente | c1 != c2 => 
		#(c1.livrosComprados & c2.livrosComprados) = 0

	//Um livro não pode estar no conteudo de dois pedidos
	all p1,p2: Pedido | p1 != p2 => 
		#(p1.conteudo & p2.conteudo) = 0

	//Livros estão com clientes, no armazém ou na carga de um drone
	all livro:Livro, arm:Armazem, cli:Cliente, ped:Pedido | (livro  !in ((arm.livros & cli.livrosComprados)+
		 (arm.livros & ped.conteudo)+ (ped.conteudo & cli.livrosComprados)))

	//A carga do drone comum não excede 3 e do especial não excede 5
	all pc:PedidoComum, pe:PedidoEspecial | #pc.conteudo <=3 and #pe.conteudo <=5

	//Todo cliente é um cliente da livraria
	all c:Cliente, livraria:Livraria | c in livraria.clientes


	#DroneEspecial = 2
	#DroneComum = 3	
}

pred show[]{}

run show for 5
