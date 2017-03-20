module livraria

sig Armazem{
	livros: set Livro,
	drones: set Drone
}

abstract sig Drone {}

sig DroneComum extends Drone{}

sig DroneEspecial extends Drone {}

abstract sig Cliente {}

sig ClienteComum extends Cliente {}

sig ClienteConveniado extends Cliente {}

sig Livro {}



fact fatos {
	#livros >= 0
	#Armazem = 1
	#DroneEspecial = 2 && #DroneComum = 3
}

pred show[]{}

run show for 5
