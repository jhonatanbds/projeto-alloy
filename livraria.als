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
	carga: set Livro
}

sig DroneComum extends Drone{}

sig DroneEspecial extends Drone {}

abstract sig Cliente {
	livrosComprados: set Livro,
	entrega: lone Drone
}

sig ClienteComum extends Cliente {
}

sig ClienteConveniado extends Cliente {	
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


fact FatosDrones {
	//Drones comuns só podem carregar até 3 livros
	all dc:DroneComum| #dc.carga <= 3

	//Drones especiais só podem carregar até 5 livros
	all de:DroneEspecial| #de.carga <= 5

	//Um drone não pode fazer duas entregas ao mesmo tempo
	all c1: Cliente, c2: Cliente | c1 != c2 => c1.entrega != c2.entrega

	//Drones estão com clientes ou no armazem
	all a: Armazem, c: Cliente, d: Drone | (d in a.drones) or (d in c.entrega)
	all a: Armazem, c:Cliente | #(a.drones & c.entrega)= 0

	//Os drones não podem estar no armazém e à caminho de um cliente ao mesmo tempo
	all cc: Cliente, a: Armazem | cc.entrega !in a.drones
	
	//Drones não podem fazer entregas vazias
	//all d:Drone, c:Cliente | some l:Livro| (d in c.entrega) => (l in d.carga)

	//Drones não podem estar ocupados com entregas e permanecerem no armazem
	all c: Cliente, a: Armazem | #(c.entrega & a.drones) = 0

	#DroneEspecial = 2
	#DroneComum = 3	
}

fact FatosLivros {
	//Um livro comprado nao pode pertencer a mais de um cliente
	all c1, c2: Cliente | c1 != c2 => 
		#(c1.livrosComprados & c2.livrosComprados) = 0

	//Um livro não pode estar no conteudo de dois drones
	all d1,d2: Drone | d1 != d2 => 
		#(d1.carga & d2.carga) = 0

	//Livros estão com clientes, no armazém ou na carga de um drone
	all livro:Livro, arm:Armazem, cli:Cliente, dro:Drone | (livro in arm.livros) or (livro in cli.livrosComprados) or (livro in dro.carga)
	all a: Armazem, c:Cliente, d: Drone | #(a.livros & c.livrosComprados) = 0 and #(c.livrosComprados & d.carga)= 0 and #(d.carga & a.livros) = 0
}

fact FatosClientes {
	//Todo cliente é um cliente da livraria
	all c:Cliente, livraria:Livraria | c in livraria.clientes

	//Clientes comuns só podem usar drones comuns, e clientes conveniados, drones especiais
	all cc: ClienteComum | cc.entrega in DroneComum	
	all cc: ClienteConveniado | cc.entrega in DroneEspecial	
}


pred show[]{}

run show for 15
