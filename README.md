## Descripción general
Esta implementación viene dada a través de agregar una nueva fase en la [última versión](https://github.com/SaraSorianoRossa/Marlin-v4) del [algoritmo de Marlin](https://github.com/arkworks-rs/marlin). 
En esta implementación se ha creado un nuevo proceso de verificar que la apertura de $t(X)$ es correcta. 
Para ello se han creado diferentes funciones en ``lib.rs``, ``prover.rs``, ``verifier.rs`` y ``mod.rs``, logrando proporcionarle la información necesaria al verificador para que pueda estar seguro de que no se comete ningún tipo de trampas.
Este proceso ha estado implementado en la última versión ya que a través de los resultados se ha visto que es la más eficiente, aún así podría crearse para cualquiera de las versiones creadas.
No se ha incorporado en todas porque en este trabajo simplemente se quería evaluar el tiempo de ejecución de este nuevo proceso independientemente del tiempo en realizar la prueba de Marlin. 
Y, por ello, para obtener los resultados con mayor rapidez se ha escogido esta última versión.

## Build
Para ejecutar este programa es necesario tener previamente instalado cargo y rust. Una vez se tienen instaladas las librerías necesarias para poder ejecutar la prueba con esta versión es necesario estar en el directorio y escribir en la terminal:
```sh
cargo build --release
```

## Test
En esta implementación, como en el resto, hay una serie de funciones para comprobar que la prueba de Marlin sigue funcionando correctamente. Para realizar estas pruebas es necesario escribir por terminal:
```sh
cargo test
```
## Todas las implementaciones
1. [Versión original](https://github.com/SaraSorianoRossa/Marlin-v1)
2. [Primera modificación](https://github.com/SaraSorianoRossa/Marlin-v2)
3. [Segunda modificación](https://github.com/SaraSorianoRossa/Marlin-v3)
4. [Tercera modificación](https://github.com/SaraSorianoRossa/Marlin-v4)
5. [Nuevo proceso inner](https://github.com/SaraSorianoRossa/New-inner)
