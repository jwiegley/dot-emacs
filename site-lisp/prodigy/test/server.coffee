net = require('net')

server = net.createServer (socket) ->
  socket.setEncoding('utf8')

  socket.on 'data', (data) ->
    [action, args...] = JSON.parse data.toString()

    switch action
      when 'log'
        console.log.apply console, args
      when 'ignore-signal'
        process.on args[0], ->
          console.log 'SIGNALING'

server.listen(process.env.PORT, '127.0.0.1')
