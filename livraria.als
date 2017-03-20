module livraria
sig Armazem{}
abstract sig Drone {}

sig DroneComum in Drone{}

sig DroneEspecial in Drone {}


fact fatos {

	#Armazem = 1

}

pred show[]{}

run show for 5
