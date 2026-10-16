
const express = require("express");
const http = require("http");
const { Server } = require("socket.io");

const app = express();
const server = http.createServer(app);

const io = new Server(server, {
  cors: {
    origin: process.env.FRONTEND_URL || "*"
  }
});

const salas = {};

app.get("/", (req, res) => {
  res.send("Servidor FUT-IA online!");
});

app.get("/health", (req, res) => {
  res.json({ status: "online" });
});

io.on("connection", (socket) => {
  socket.on("criar-sala", ({ nome, time }, callback) => {
    const codigo = Math.random().toString(36).substring(2, 8).toUpperCase();

    salas[codigo] = {
      jogadores: [],
      espectadores: []
    };

    entrarNaSala(socket, codigo, nome, time, callback);
  });

  socket.on("entrar-sala", ({ codigo, nome, time }, callback) => {
    entrarNaSala(socket, codigo.toUpperCase(), nome, time, callback);
  });

  socket.on("disconnect", () => {
    for (const codigo in salas) {
      const sala = salas[codigo];

      sala.jogadores = sala.jogadores.filter(p => p.id !== socket.id);
      sala.espectadores = sala.espectadores.filter(p => p.id !== socket.id);

      if (sala.jogadores.length === 0 && sala.espectadores.length === 0) {
        delete salas[codigo];
      } else {
        io.to(codigo).emit("atualizar-sala", sala);
      }
    }
  });
});

function entrarNaSala(socket, codigo, nome, time, callback) {
  const sala = salas[codigo];

  if (!sala) {
    return callback({ erro: "Sala não encontrada." });
  }

  const espectador = time === "espectador";

  if (espectador && sala.espectadores.length >= 5) {
    return callback({ erro: "Sala cheia de espectadores." });
  }

  if (!espectador && !["time1", "time2"].includes(time)) {
    return callback({ erro: "Escolha um time válido." });
  }

  if (!espectador && sala.jogadores.filter(p => p.time === time).length >= 5) {
    return callback({ erro: "Esse time já está cheio." });
  }

  const participante = {
    id: socket.id,
    nome: String(nome || "Jogador").slice(0, 20),
    time
  };

  if (espectador) {
    sala.espectadores.push(participante);
  } else {
    sala.jogadores.push(participante);
  }

  socket.join(codigo);

  callback({ sucesso: true, codigo, sala });
  io.to(codigo).emit("atualizar-sala", sala);
}

const porta = process.env.PORT || 3000;

server.listen(porta, "0.0.0.0", () => {
  console.log(`FUT-IA online na porta ${porta}`);
});
